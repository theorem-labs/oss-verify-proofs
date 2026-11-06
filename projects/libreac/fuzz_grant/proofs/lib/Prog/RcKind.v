From Stdlib Require Import String Ascii ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Import ListNotations.
Open Scope Z_scope.

Definition KL1 (x : Z) : Z :=
  if x =? 0 then 2
  else if x =? 1 then 3
  else if x =? 16 then 10
  else if x =? 128 then 9
  else if x =? 129 then 7
  else if x =? 130 then 9
  else if x =? 132 then 9
  else 13.

Definition kind_names : list string :=
  ["none"; "filler"; "scene_transfer"; "master_hb"; "master_announce"; "grant"; "headamp"; "box_hb";
   "split_announce"; "config_announce"; "group_map"; "record_fragment"; "link2"; "unknown_ctrl"]%string.

Definition kind_name (x : Z) : string :=
  if x <=? 13 then nth (Z.to_nat x) kind_names "?"%string else "?"%string.

Definition cstr_bytes (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_N (N_of_ascii c))) (list_ascii_of_string s) ++ [Z_to_bv 8 0].
