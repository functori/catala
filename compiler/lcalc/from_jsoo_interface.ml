(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020 Inria, contributor:
   Denis Merigoux <denis.merigoux@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

open Catala_utils
open Shared_ast

let pp dest fmt = Format.kdprintf (fun k -> List.iter k dest) fmt

let method_name = function
  | "" -> invalid_arg "empty method name"
  | s ->
    let s = if String.contains s '_' then s ^ "_" else s in
    let code = Char.code (String.get s 0) in
    if code >= 65 && code <= 90 then "_" ^ s else s

let format_struct_field_name fmt n =
  let s = Format.asprintf "%a" To_ocaml.format_struct_field_name n in
  Format.fprintf fmt "%s" (method_name s)

let format_enum_cons_name fmt v =
  let s = Format.asprintf "%a" To_ocaml.format_enum_cons_name v in
  Format.fprintf fmt "%s" (method_name s)

let typ_needs_parens (e : typ) : bool =
  match Mark.remove e with TArrow _ | TArray _ -> true | _ -> false

let format_to_module_name fmt s =
  let p, i =
    match s with
    | `Sname s -> StructName.path s, StructName.get_info s
    | `Ename s -> EnumName.path s, EnumName.get_info s
    | `Aname s -> AbstractType.path s, AbstractType.get_info s
  in
  Format.fprintf fmt "%a%a"
    (Format.pp_print_list
       ~pp_sep:(fun _ () -> ())
       (fun ppf m -> Format.fprintf ppf "%a." Uid.Module.format m))
    p Uid.MarkedString.format i

let format_typ (fmt : Format.formatter) (typ : typ) : unit =
  let rec aux bctx fmt typ =
    let format_typ_with_parens (fmt : Format.formatter) (t : typ) =
      if typ_needs_parens t then Format.fprintf fmt "(%a)" (aux bctx) t
      else Format.fprintf fmt "%a" (aux bctx) t
    in
    match Mark.remove typ with
    | TLit l -> Format.fprintf fmt "%a_jsoo" Print.tlit l
    | TTuple [] -> Format.fprintf fmt "unit"
    | TTuple _ -> Format.fprintf fmt "Js.Unsafe.any Js.js_array Js.t"
    | TStruct s -> Format.fprintf fmt "%a.jsoo" format_to_module_name (`Sname s)
    | TOption t ->
      Format.fprintf fmt "@[<hov 2>(%a)@] Optional.jsoo" format_typ_with_parens
        t
    | TDefault t -> aux bctx fmt t
    | TEnum e -> Format.fprintf fmt "%a.jsoo" format_to_module_name (`Ename e)
    | TAbstract e ->
      Format.fprintf fmt "%a.jsoo" format_to_module_name (`Aname e)
    | TArrow (t1, t2) ->
      Format.fprintf fmt "@[<hov 2>%a@]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt " ->@ ")
           format_typ_with_parens)
        (t1 @ [t2])
    | TArray t1 ->
      Format.fprintf fmt "@[%a@ Js.js_array Js.t@]" format_typ_with_parens t1
    | TVar v ->
      let name = Bindlib.name_of v in
      let name =
        if String.starts_with ~prefix:"'" name then
          "a" ^ String.sub name 1 (String.length name - 1)
        else "t" ^ name
      in
      Format.fprintf fmt "'%s" name
    | TForAll tb ->
      let _v, typ, bctx = Bindlib.unmbind_in bctx tb in
      aux bctx fmt typ
    | TClosureEnv -> Format.fprintf fmt "Js.Unsafe.any"
    | TError -> assert false
  in
  aux Bindlib.empty_ctxt fmt typ

let rec format_typ_of (fmt : Format.formatter) (typ : typ) : unit =
  let rec aux bctx fmt typ =
    match Mark.remove typ with
    | TLit l -> Format.fprintf fmt "%a_of_jsoo" Print.tlit l
    | TTuple [] -> Format.fprintf fmt "unit_of_jsoo"
    | TTuple l ->
      let i = ref (-1) in
      Format.fprintf fmt "@[<hov 2>(fun js ->@,(%a))@]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
           (fun fmt t ->
             incr i;
             Format.fprintf fmt
               "(@[<hov>let v = Js.Optdef.to_option (Js.array_get js %d) in@;\
                <1 0>match v with@;\
                <1 0>| None -> invalid_arg \"no value in tuple position %d\"@;\
                <1 0>| Some v -> %a (Js.Unsafe.coerce v)@])"
               !i !i (aux bctx) t))
        l
    | TStruct s ->
      Format.fprintf fmt "%a.of_jsoo" format_to_module_name (`Sname s)
    | TOption t ->
      Format.fprintf fmt "(fun x -> Optional.of_jsoo %a x)" (aux bctx) t
    | TDefault t -> aux bctx fmt t
    | TEnum e ->
      Format.fprintf fmt "%a.of_jsoo" format_to_module_name (`Ename e)
    | TAbstract e ->
      Format.fprintf fmt "%a.of_jsoo" format_to_module_name (`Aname e)
    | TArrow (t1, t2) ->
      let ip, ie = ref (-1), ref (-1) in
      Format.fprintf fmt "(fun f -> (fun %a -> %a (f %a)))"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
           (fun fmt _t ->
             incr ip;
             Format.fprintf fmt "_x%d" !ip))
        t1 (aux bctx) t2
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
           (fun fmt t ->
             incr ie;
             Format.fprintf fmt "(%a _x%d)" format_typ_of t !ie))
        t1
    | TArray t1 -> (
      match Mark.remove t1 with
      | TVar _ | TClosureEnv -> Format.fprintf fmt "Js.to_array"
      | _ ->
        Format.fprintf fmt "(fun js -> Array.map %a (Js.to_array js))"
          (aux bctx) t1)
    | TVar _ -> Format.fprintf fmt "Fun.id"
    | TForAll tb ->
      let _v, typ, bctx = Bindlib.unmbind_in bctx tb in
      aux bctx fmt typ
    | TClosureEnv -> Format.fprintf fmt "Unsafe.coerce"
    | TError -> assert false
  in
  aux Bindlib.empty_ctxt fmt typ

let format_struct_field_typ (fmt : Format.formatter) (typ : typ) : unit =
  Format.fprintf fmt "@[<hov 2>%a@] Js.prop" format_typ typ

let format_struct_field_of
    var
    (fmt : Format.formatter)
    ((name, typ) : StructField.t * typ) : unit =
  Format.fprintf fmt "%a (%s ##. %a)" format_typ_of typ var
    format_struct_field_name (None, name)

let format_var ppf var =
  let string_var = Format.asprintf "%a" To_ocaml.format_var var in
  let input_var = if string_var = "_" then "custom_jsoo_var" else string_var in
  Format.fprintf ppf "%s" input_var

let js_object_name = String.uncapitalize_ascii

let rec format_typ_to (fmt : Format.formatter) (typ : typ) : unit =
  let rec aux bctx fmt typ =
    match Mark.remove typ with
    (* Ca ca vient du runtime donc pas de soucis*)
    | TLit l -> Format.fprintf fmt "%a_to_jsoo" Print.tlit l
    | TTuple [] -> Format.fprintf fmt "unit_to_jsoo"
    | TTuple l ->
      let ip, ie = ref (-1), ref (-1) in
      Format.fprintf fmt "(fun @[<h>(%a)@] -> Js.array @[<hov 2>[|%a|]@])"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
           (fun fmt _t ->
             incr ip;
             Format.fprintf fmt "_t%d" !ip))
        l
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ")
           (fun fmt t ->
             incr ie;
             Format.fprintf fmt "Js.Unsafe.inject (%a _t%d)" (aux bctx) t !ie))
        l
    | TStruct s ->
      Format.fprintf fmt "%a.to_jsoo" format_to_module_name (`Sname s)
    | TOption t ->
      Format.fprintf fmt "(fun x -> Optional.to_jsoo %a x)" (aux bctx) t
    | TDefault t -> aux bctx fmt t
    | TEnum e ->
      Format.fprintf fmt "%a.to_jsoo" format_to_module_name (`Ename e)
    | TAbstract e ->
      Format.fprintf fmt "%a.to_jsoo" format_to_module_name (`Aname e)
    | TArrow (t1, t2) ->
      let ip, ie = ref (-1), ref (-1) in
      Format.fprintf fmt "(fun f -> (fun %a -> %a (f %a)))"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
           (fun fmt _t ->
             incr ip;
             Format.fprintf fmt "_x%d" !ip))
        t1 (aux bctx) t2
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
           (fun fmt t ->
             incr ie;
             Format.fprintf fmt "(%a _x%d)" format_typ_to t !ie))
        t1
    | TArray t1 -> (
      match Mark.remove t1 with
      | TVar _ | TClosureEnv -> Format.fprintf fmt "Js.array"
      | _ ->
        Format.fprintf fmt "(fun a -> Js.array (Array.map %a a))" (aux bctx) t1)
    | TVar _ -> Format.fprintf fmt "Fun.id"
    | TForAll tb ->
      let _v, typ, bctx = Bindlib.unmbind_in bctx tb in
      aux bctx fmt typ
    | TClosureEnv -> Format.fprintf fmt "Unsafe.inject"
    | TError -> assert false
  in
  aux Bindlib.empty_ctxt fmt typ

let format_struct_field_to
    ?struct_name
    var
    (fmt : Format.formatter)
    ((name, typ) : StructField.t * typ) : unit =
  Format.fprintf fmt "%a %s.%a" format_typ_to typ var
    To_ocaml.format_struct_field_name (struct_name, name)

let format_ctx
    (type_ordering : TypeIdent.t list)
    (ppml : Format.formatter)
    (ppi : Format.formatter)
    (ctx : decl_ctx) : unit =
  let format_struct_decl (struct_name, struct_fields) =
    if TypeIdent.(Set.mem (Struct struct_name) ctx.ctx_public_types) then
      let fields = StructField.Map.bindings struct_fields in
      if StructField.Map.is_empty struct_fields then (
        Format.fprintf ppi
          "@[<v 2>module %a : sig@,\
           type t = unit@,\
           type jsoo = unit@,\
           val to_jsoo : t -> jsoo@,\
           val of_jsoo : jsoo -> t@;\
           <1 -2>end@]@,\
           @,"
          To_ocaml.format_to_module_name (`Sname struct_name);
        Format.fprintf ppml
          "@[<v 2>module %a = struct@,\
           type t = unit@,\
           type jsoo = unit@,\
           let to_jsoo = Fun.id@,\
           let of_jsoo = Fun.id@;\
           <1 -2>end@]@,\
           @,"
          To_ocaml.format_to_module_name (`Sname struct_name))
      else
        (Format.fprintf ppi
           "@[<v 2>module %a : sig@,\
            @[<hv 2>type t = {@,\
            %a@;\
            <0-2>}@]@;\
            @[<hv 2>class type jsoo_ct = object@;\
            <1 0>%a@;\
            <1 -2>end@]@,\
            type jsoo = jsoo_ct Js.t@,\
            val to_jsoo : t -> jsoo@,\
            val of_jsoo : jsoo -> t@;\
            <1 -2>end@]@,\
            @,"
           To_ocaml.format_to_module_name (`Sname struct_name)
           (Format.pp_print_list
              ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ")
              (fun fmt (struct_field, struct_field_type) ->
                Format.fprintf fmt "@[<hov 2>%a:@ %a@]"
                  To_ocaml.format_struct_field_name (None, struct_field)
                  To_ocaml.format_typ struct_field_type))
           fields
           (Format.pp_print_list
              ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
              (fun fmt (struct_field, struct_field_type) ->
                Format.fprintf fmt "@[<hov 2>method %a:@ %a@]"
                  format_struct_field_name (None, struct_field)
                  format_struct_field_typ struct_field_type))
           fields;
         Format.fprintf ppml
           "@[<v 2>module %a = struct@,\
            @[<hv 2>type t = {@,\
            %a@;\
            <0-2>}@]@;\
            @[<hv 2>class type jsoo_ct = object@;\
            <1 0>%a@;\
            <1 -2>end@]@,\
            type jsoo = jsoo_ct Js.t@,\
            @[<hv 2>let to_jsoo x = object%%js@;\
            <1 0>%a@;\
            <1 -2>end@]@;\
            @[<hv 2>let of_jsoo js = {@;\
            %a@;\
            <0 -2>}@]@;\
            <1 -2>end@]@,\
            @,"
           To_ocaml.format_to_module_name (`Sname struct_name)
           (Format.pp_print_list
              ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ")
              (fun fmt (struct_field, struct_field_type) ->
                Format.fprintf fmt "@[<hov 2>%a:@ %a@]"
                  To_ocaml.format_struct_field_name (None, struct_field)
                  To_ocaml.format_typ struct_field_type))
           fields
           (Format.pp_print_list
              ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
              (fun fmt (struct_field, struct_field_type) ->
                Format.fprintf fmt "@[<hov 2>method %a:@ %a@]"
                  format_struct_field_name (None, struct_field)
                  format_struct_field_typ struct_field_type))
           fields)
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
             (fun fmt (struct_field, struct_field_type) ->
               Format.fprintf fmt "@[<hov 2>val mutable %a =@ %a@]"
                 format_struct_field_name (None, struct_field)
                 (format_struct_field_to "x")
                 (struct_field, struct_field_type)))
          fields
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ")
             (fun fmt (struct_field, struct_field_type) ->
               Format.fprintf fmt "@[<hov 2>%a =@ %a@]"
                 To_ocaml.format_struct_field_name (None, struct_field)
                 (format_struct_field_of "js")
                 (struct_field, struct_field_type)))
          fields
  in
  let format_enum_decl (enum_name, enum_cons) =
    if TypeIdent.(Set.mem (Enum enum_name) ctx.ctx_public_types) then
      let variants = EnumConstructor.Map.bindings enum_cons in
      let string_enum =
        EnumConstructor.Map.for_all
          (fun _ -> (function TLit TUnit, _ -> true | _ -> false))
          enum_cons
      in
      if string_enum then (
        Format.fprintf ppi
          "@[<hv 2>module %a : sig@ @[<hv 2>type t =@ %a%a%a@]@,\
           type jsoo = Js.js_string Js.t@,\
           val to_jsoo : t -> jsoo@,\
           val of_jsoo : jsoo -> t@;\
           <1 -2>end@]@,\
           @,"
          To_ocaml.format_to_module_name (`Ename enum_name)
          Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, enum_cons_type) ->
               match enum_cons_type with
               | TLit TUnit, _ ->
                 Format.fprintf fmt "@[<hov 2>%a@]"
                   To_ocaml.format_enum_cons_name enum_cons
               | _ ->
                 Format.fprintf fmt "@[<hov 2>%a of@ %a@]"
                   To_ocaml.format_enum_cons_name enum_cons To_ocaml.format_typ
                   enum_cons_type))
          variants;
        Format.fprintf ppml
          "@[<hv 2>module %a = struct@ @[<hv 2>type t =@ %a%a%a@]@,\
           type jsoo = Js.js_string Js.t@,\
           @[<hv 2>let to_jsoo x = Js.string (match x with %a%a%a)@]@,\
           @[<hv 2>let of_jsoo js = match Js.to_string js with %a%a%a@,\
           @ |@[<hov> s -> invalid_arg (Format.sprintf \"unknown case in enum: \
           %%S\" s)@]@]@;\
           <1 -2>end@]@,\
           @,"
          To_ocaml.format_to_module_name (`Ename enum_name)
          Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, enum_cons_type) ->
               match enum_cons_type with
               | TLit TUnit, _ ->
                 Format.fprintf fmt "@[<hov 2>%a@]"
                   To_ocaml.format_enum_cons_name enum_cons
               | _ ->
                 Format.fprintf fmt "@[<hov 2>%a of@ %a@]"
                   To_ocaml.format_enum_cons_name enum_cons To_ocaml.format_typ
                   enum_cons_type))
          variants Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, _) ->
               Format.fprintf fmt "@[<hov 2>%a -> \"%a\"@]"
                 To_ocaml.format_enum_cons_name enum_cons
                 To_ocaml.format_enum_cons_name enum_cons))
          variants Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, _) ->
               Format.fprintf fmt "@[<hov 2>\"%a\" -> %a@]"
                 To_ocaml.format_enum_cons_name enum_cons
                 To_ocaml.format_enum_cons_name enum_cons))
          variants)
      else (
        Format.fprintf ppi
          "@[<hv 2>module %a : sig@ @[<hv 2>type t =@ %a%a%a@]@,\
           @[<hv 2>class type jsoo_ct = object@;\
           <1 0>%a@;\
           <1 -2>end@]@,\
           type jsoo = jsoo_ct Js.t@,\
           val to_jsoo : t -> jsoo@,\
           val of_jsoo : jsoo -> t@;\
           <1 -2>end@]@,\
           @,"
          To_ocaml.format_to_module_name (`Ename enum_name)
          Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, enum_cons_type) ->
               match enum_cons_type with
               | TLit TUnit, _ ->
                 Format.fprintf fmt "@[<hov 2>%a@]"
                   To_ocaml.format_enum_cons_name enum_cons
               | _ ->
                 Format.fprintf fmt "@[<hov 2>%a of@ %a@]"
                   To_ocaml.format_enum_cons_name enum_cons To_ocaml.format_typ
                   enum_cons_type))
          variants
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
             (fun fmt (enum_cons, enum_cons_type) ->
               Format.fprintf fmt "@[<hov 2>method %a :@ %a Js.optdef Js.prop@]"
                 format_enum_cons_name enum_cons format_typ enum_cons_type))
          variants;
        Format.fprintf ppml
          "@[<hv 2>module %a = struct@ @[<hv 2>type t =@ %a%a%a@]@,\
           @[<hv 2>class type jsoo_ct = object@;\
           <1 0>%a@;\
           <1 -2>end@]@,\
           type jsoo = jsoo_ct Js.t@,\
           @[<hv 2>let to_jsoo x = match x with %a%a%a@]@,\
           @[<hv 2>let of_jsoo js = match %a with@;\
           %a%a%a@,\
           @ |@[<hov> _ -> invalid_arg \"unknown case\"@]@]@;\
           <1 -2>end@]@,\
           @,"
          To_ocaml.format_to_module_name (`Ename enum_name)
          Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, enum_cons_type) ->
               match enum_cons_type with
               | TLit TUnit, _ ->
                 Format.fprintf fmt "@[<hov 2>%a@]"
                   To_ocaml.format_enum_cons_name enum_cons
               | _ ->
                 Format.fprintf fmt "@[<hov 2>%a of@ %a@]"
                   To_ocaml.format_enum_cons_name enum_cons To_ocaml.format_typ
                   enum_cons_type))
          variants
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
             (fun fmt (enum_cons, enum_cons_type) ->
               Format.fprintf fmt "@[<hov 2>method %a :@ %a Js.optdef Js.prop@]"
                 format_enum_cons_name enum_cons format_typ enum_cons_type))
          variants Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, enum_cons_type) ->
               let no_content =
                 match enum_cons_type with TLit TUnit, _ -> true | _ -> false
               in
               Format.fprintf fmt
                 "@[<hov 2>%a%a -> object%%js@;<1 0>%a@;<1 -2>end@]@,"
                 To_ocaml.format_enum_cons_name enum_cons
                 (fun fmt b -> if not b then Format.fprintf fmt "@ x")
                 no_content
                 (Format.pp_print_list
                    ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
                    (fun fmt (enum_cons2, _) ->
                      if enum_cons <> enum_cons2 then
                        Format.fprintf fmt
                          "@[<hov 2>val mutable %a =@ Js.undefined@]@,"
                          format_enum_cons_name enum_cons2
                      else
                        Format.fprintf fmt
                          "@[<hov 2>val mutable %a =@ Js.def (%a@ %a)@]@,"
                          format_enum_cons_name enum_cons format_typ_to
                          enum_cons_type
                          (fun fmt b ->
                            if not b then Format.fprintf fmt "x"
                            else Format.fprintf fmt "()")
                          no_content))
                 variants))
          variants
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
             (fun fmt (enum_cons, _) ->
               Format.fprintf fmt "@[<hov 2>Js.Optdef.to_option (js##.%a)@]"
                 format_enum_cons_name enum_cons))
          variants Format.pp_print_if_newline () Format.pp_print_string "| "
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ | ")
             (fun fmt (enum_cons, enum_cons_type) ->
               let no_content =
                 match enum_cons_type with TLit TUnit, _ -> true | _ -> false
               in
               Format.fprintf fmt "@[<hov 2>%a -> %a%a@]@,"
                 (Format.pp_print_list
                    ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
                    (fun fmt (enum_cons2, _) ->
                      if enum_cons <> enum_cons2 then Format.fprintf fmt "_"
                      else Format.fprintf fmt "Some _c"))
                 variants To_ocaml.format_enum_cons_name enum_cons
                 (fun fmt b ->
                   if not b then
                     Format.fprintf fmt "@ (%a _c)" format_typ_of enum_cons_type)
                 no_content))
          variants)
  in
  let is_in_type_ordering s =
    List.exists
      (fun struct_or_enum ->
        match struct_or_enum with
        | TypeIdent.Enum _ | TypeIdent.Abstract _ -> false
        | TypeIdent.Struct s' -> s = s')
      type_ordering
  in
  let scope_structs =
    List.map
      (fun (s, _) -> TypeIdent.Struct s)
      (StructName.Map.bindings
         (StructName.Map.filter
            (fun s _ -> not (is_in_type_ordering s))
            ctx.ctx_structs))
  in
  List.iter
    (function
      | TypeIdent.Struct s ->
        let def = StructName.Map.find s ctx.ctx_structs in
        if StructName.path s = [] then format_struct_decl (s, def)
      | TypeIdent.Enum e ->
        if EnumName.equal e Expr.option_enum then ()
        else
          let def = EnumName.Map.find e ctx.ctx_enums in
          if EnumName.path e = [] then format_enum_decl (e, def)
      | _ -> ())
    (type_ordering @ scope_structs)

let format_code_items
    (module_name : string)
    (ppml : Format.formatter)
    (ppi : Format.formatter)
    (code_items : 'm Ast.expr code_item_list) =
  let js_object = js_object_name module_name in
  pp [ppml; ppi] "@[<v>";
  let _exports =
    BoundList.iter code_items ~f:(fun var item ->
        match item with
        | Topdef (_name, typ, vis, _e) ->
          if vis = Public then (
            (* J'imagine que ca en js ca doit pouvoir se transposer en
               property*)
            Format.fprintf ppi "@,@[<hov 2>val %a : %a@]@," format_var var
              To_ocaml.format_typ typ;
            let rec aux bctx typ =
              match Mark.remove typ with
              | TArrow (lt, te) | TDefault (TArrow (lt, te), _) ->
                let ip, ie = ref (-1), ref (-1) in
                Format.fprintf ppml
                  "@,\
                   @[<v 2>@[<hov 2>let %a : %a =@]@ fun %a -> %a(%s##%a_ %a)@]@,"
                  format_var var To_ocaml.format_typ typ
                  (Format.pp_print_list
                     ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
                     (fun fmt _t ->
                       incr ip;
                       Format.fprintf fmt "_x%d" !ip))
                  lt format_typ_of te js_object format_var var
                  (Format.pp_print_list
                     ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
                     (fun fmt t ->
                       incr ie;
                       Format.fprintf fmt "(%a _x%d)" format_typ_to t !ie))
                  lt
              | TForAll tb ->
                let _v, typ, bctx = Bindlib.unmbind_in bctx tb in
                aux bctx typ
              | _ ->
                Format.fprintf ppml
                  "@,@[<v 2>@[<hov 2>let %a : %a =@]@ %a %s##.%a_@]@,"
                  format_var var To_ocaml.format_typ typ format_typ_of typ
                  js_object format_var var
            in
            aux Bindlib.empty_ctxt typ)
        | ScopeDef (_name, body) ->
          (* Ca c'est quand tu déclares un champ d'application *)
          if body.scope_body_visibility = Public then (
            let scope_input_var, _scope_body_expr =
              Bindlib.unbind body.scope_body_expr
            in
            let input_var =
              let string_var =
                Format.asprintf "%a" format_var scope_input_var
              in
              if string_var = "_" then "x" else string_var
            in
            Format.fprintf ppi
              "@,@[<hv 2>val %a_jsoo :@ @[<hv>%a.jsoo ->@ %a.jsoo@]@]@,"
              format_var var format_to_module_name
              (`Sname body.scope_body_input_struct) format_to_module_name
              (`Sname body.scope_body_output_struct);
            Format.fprintf ppml
              "@,\
               @[<hv 2>@[<hov 2>let %a_jsoo :@ %a.jsoo -> %a.jsoo =@ fun %s \
               ->@]@ %a.to_jsoo (%a (%a.of_jsoo %s))@]@,"
              format_var var format_to_module_name
              (`Sname body.scope_body_input_struct) format_to_module_name
              (`Sname body.scope_body_output_struct) input_var
              format_to_module_name (`Sname body.scope_body_output_struct)
              format_var var format_to_module_name
              (`Sname body.scope_body_input_struct) input_var))
  in
  ();
  pp [ppml; ppi] "@]"

let export_code_items ppml modname exports =
  Format.fprintf ppml "@[<hv 2>let () = %a (object%%js@;<1 0>%a@;<1 -2>end)@]"
    (fun fmt m ->
      match m with
      | None -> Format.fprintf fmt "Js.export_all"
      | Some m -> Format.fprintf fmt "Js.export \"%s\"" m)
    modname
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt "@,")
       (fun fmt e ->
         match e with
         | `top v ->
           Format.fprintf fmt "@[<hov 2>val %s =@ %s_jsoo@]" (method_name v) v
         | `scope f ->
           Format.fprintf fmt "@[<hov 2>method %s x =@ %s_jsoo x@]"
             (method_name f) f))
    exports

let format_module_registration fmt modname hash is_external =
  Format.pp_open_vbox fmt 2;
  Format.pp_print_string fmt "let () =";
  Format.pp_print_space fmt ();
  Format.pp_open_hvbox fmt 2;
  Format.fprintf fmt "Catala_runtime.register_module \"%a\"" ModuleName.format
    modname;
  Format.pp_print_space fmt ();
  Format.pp_open_vbox fmt 2;
  Format.pp_print_string fmt "[]";
  Format.pp_print_space fmt ();
  Format.fprintf fmt "\"%a\""
    (fun ppf h ->
      if is_external then Format.pp_print_string ppf Hash.external_placeholder
      else Hash.format ppf h)
    hash;
  Format.pp_close_box fmt ();
  Format.pp_close_box fmt ();
  Format.pp_print_newline fmt ()

let format_program
    output_file
    ppml
    ~(hashf : Hash.t -> Hash.full)
    (p : 'm Ast.program)
    (type_ordering : TypeIdent.t list) : unit =
  File.with_secondary_out_channel ~output_file ~ext:"mli"
  @@ fun intf_file ppi ->
  let modname =
    match p.module_name, output_file with
    | Some (n, _), _ -> Some (ModuleName.to_string n)
    | None, Some filename ->
      Some
        (String.capitalize_ascii (String.to_id File.(basename filename -.- "")))
    | _ -> None
  in
  let module_name = Option.value modname ~default:"NoName" in
  pp [ppml; ppi]
    "@[<v>[%@%@%@ocaml.warning \"-4-26-27-32-33-34-37-41-42-69\"]@,\
     @,\
    \     open Js_of_ocaml@,\
    \     open Catala_runtime@,\
    \     open Catala_runtime_jsoo@,\
     @,";
  pp [ppml] "%a"
    (fun fmt -> function
      | None -> ()
      | Some obj ->
        Format.fprintf fmt "let %s = (Js.Unsafe.js_expr \"%s\")@,"
          (js_object_name obj) obj)
    modname;
  format_ctx type_ordering ppml ppi p.decl_ctx;
  format_code_items module_name ppml ppi p.code_items;
  p.module_name
  |> Option.iter (fun (modname, intf_id) ->
      format_module_registration ppml modname (hashf intf_id.hash) true);
  pp [ppml; ppi] "@]";
  Format.pp_print_flush ppml ();
  Format.pp_print_flush ppi ();
  Option.iter Ocamlformat.format output_file;
  Option.iter Ocamlformat.format intf_file

let lit_mock_var_js (l : typ_lit) : string =
  match l with
  | TUnit -> "0"
  | TBool -> "true"
  | TInt -> "0n"
  | TRat -> "{n : 0n, d: 0n}"
  | TMoney -> "0n"
  | TDuration -> "{ years: 1, months: 1, days: 1 }"
  | TDate -> "{ year: 1970, month: 1, day: 1 }"
  | TPos ->
    {|{fileName : "file", startLine: 0, endLine: 0, endColumn: 0, lawHeadings: []}|}

let format_mock_var_js (ctx : decl_ctx) (fmt : Format.formatter) (typ : typ) :
    unit =
  let rec aux bctx fmt typ =
    match Mark.remove typ with
    | TLit l -> Format.fprintf fmt "%s" (lit_mock_var_js l)
    | TTuple [] -> Format.fprintf fmt "[]"
    | TTuple typs ->
      Format.fprintf fmt "[%a]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
           (aux bctx))
        typs
    | TStruct _s -> Format.fprintf fmt "{}"
    | TOption t -> Format.fprintf fmt "@[<v 2>[%a]@]" (aux bctx) t
    | TDefault t -> aux bctx fmt t
    | TEnum e ->
      let every_cons = EnumName.Map.find e ctx.ctx_enums in
      let variant, typ =
        EnumConstructor.Map.find_first (fun _ -> true) every_cons
      in
      Format.fprintf fmt "{%a: %a}" EnumConstructor.format variant (aux bctx)
        typ
    | TAbstract _e -> Format.fprintf fmt "0"
    | TArrow (t1, t2) ->
      Format.fprintf fmt "@[<v 2>(%a)@]"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           (aux bctx))
        (t1 @ [t2])
    | TArray t1 -> Format.fprintf fmt "[@,%a@]@,]" (aux bctx) t1
    | TVar v ->
      let name = Bindlib.name_of v in
      let name =
        if String.starts_with ~prefix:"'" name then
          "a" ^ String.sub name 1 (String.length name - 1)
        else "t" ^ name
      in
      Format.fprintf fmt "'%s" name
    | TForAll tb ->
      let _v, typ, bctx = Bindlib.unmbind_in bctx tb in
      aux bctx fmt typ
    | TClosureEnv -> Format.fprintf fmt "Js.Unsafe.any"
    | TError -> assert false
  in
  aux Bindlib.empty_ctxt fmt typ

let format_code_items_js
    (ctx : decl_ctx)
    (ppjs : Format.formatter)
    (code_items : 'm Ast.expr code_item_list) =
  pp [ppjs] "@[<v>";
  let _exports =
    BoundList.iter code_items ~f:(fun var item ->
        match item with
        | Topdef (_name, typ, vis, _e) ->
          if vis = Public then
            let rec aux bctx typ =
              match Mark.remove typ with
              | TArrow (lt, te) | TDefault (TArrow (lt, te), _) ->
                let ip, _ie = ref (-1), ref (-1) in
                Format.fprintf ppjs
                  "@[<v 2>%a: function(%a){@,@[<v 2>return %a;@]@]@,},@,"
                  format_var var
                  (Format.pp_print_list
                     ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ,")
                     (fun fmt _t ->
                       incr ip;
                       Format.fprintf fmt "_param%d" !ip))
                  lt (format_mock_var_js ctx) te
              | TForAll tb ->
                let _v, typ, bctx = Bindlib.unmbind_in bctx tb in
                aux bctx typ
              | _ ->
                Format.fprintf ppjs "@[<v 2>%a: %a@]" format_var var
                  (format_mock_var_js ctx) typ
            in
            aux Bindlib.empty_ctxt typ
        | ScopeDef (_name, _body) -> ())
  in
  pp [ppjs] "@]"

let format_js_template ppjs name (p : 'm Ast.program) : unit =
  pp [ppjs]
    "// Mock for the catala external: %s\n\
     //\n\
     // This file must be loaded before the js file containing the call to the \
     external contract (with a <script> balise or a require).\n"
    name;
  Option.fold
    ~none:(pp [ppjs] "@[<v 2>{@,%a}]")
    ~some:(fun (modname, _) ->
      pp [ppjs] "@[<v 2>globalThis.%s = {@,%a@]@,}"
        (ModuleName.to_string modname))
    p.module_name
    (format_code_items_js p.decl_ctx)
    p.code_items
