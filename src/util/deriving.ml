module Pervasives = struct
  open Pervasives
  type 'a ref = [%import: 'a Pervasives.ref] [@@deriving yojson]
end
module Cil = struct
  open Cil (* can't include because of type defintions below... *)

  let stmt_to_yojson x = `Int (x.sid)
  let varinfo_to_yojson x = `String (x.vname)

  type location = [%import: Cil.location]
  (*and stmt = [%import: Cil.stmt]*)
  and stmtkind = [%import: Cil.stmtkind]
  and label = [%import: Cil.label]
  and instr = [%import: Cil.instr]
  and exp = [%import: Cil.exp]
  and block = [%import: Cil.block]
  and lval = [%import: Cil.lval]
  and lhost = [%import: Cil.lhost]
  (*and varinfo = [%import: Cil.varinfo]*)
  and offset = [%import: Cil.offset]
  and attributes = [%import: Cil.attributes]
  and attribute = [%import: Cil.attribute]
  and constant = [%import: Cil.constant]
  and typ = [%import: Cil.typ]
  and unop = [%import: Cil.unop]
  and binop = [%import: Cil.binop]
  and initinfo = [%import: Cil.initinfo]
  and storage = [%import: Cil.storage]
  and fieldinfo = [%import: Cil.fieldinfo]
  and attrparam = [%import: Cil.attrparam]
  and ikind = [%import: Cil.ikind]
  and fkind = [%import: Cil.fkind]
  and enuminfo = [%import: Cil.enuminfo]
  and typeinfo = [%import: Cil.typeinfo]
  and compinfo = [%import: Cil.compinfo]
  and init = [%import: Cil.init]
  and typsig = [%import: Cil.typsig]
  and fundec = [%import: Cil.fundec]
  [@@deriving to_yojson]

  let pp_varinfo fmt v = Format.fprintf fmt "%s" v.vname
  let show_varinfo v = v.vname
end