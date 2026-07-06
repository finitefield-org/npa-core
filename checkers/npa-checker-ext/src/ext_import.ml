type entry = {
  module_name : Ext_name.t;
  export_hash : Ext_hash.digest;
  certificate_hash : Ext_hash.digest option;
}

type store = entry list

let empty = []
