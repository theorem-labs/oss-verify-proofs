From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Module LoTailAddr.
  Definition pc_tail : Z := 0x14a3c.
  Definition pc_bd : Z := 0x14cb0.
  Definition pc_ret : Z := 0x13ba0.
  Definition pc_epi : Z := 0x13b60.
  Definition pc_trap : Z := 0x14e60.

  Definition c_fs : Z := 0x152cc.
  Definition c_vr : Z := 0x167f8.
  Definition c_vf : Z := 0x15840.
  Definition c_bd : Z := 0x15be4.
  Definition c_fu : Z := 0x158f4.

  Definition ra_fs : Z := 0x14a48.
  Definition ra_cv : Z := 0x14b00.
  Definition ra_vf : list Z := [0x14ba4; 0x14bd4; 0x14c04; 0x14c34; 0x14c64; 0x14c98; 0x14e18; 0x14e4c].
  Definition ra_bd : Z := 0x14cb8.
  Definition ra_fu : Z := 0x14dfc.
  Definition ra_fl : Z := 0x14cf8.
  Definition ra_fd : Z := 0x14d3c.
  Definition ra_fa : Z := 0x14d98.

  Definition pc_col : Z := 0x14ae8.
  Definition pc_desA : Z := 0x14d18.
  Definition pc_desB : Z := 0x14d64.
  Definition pc_memset : Z := 0x14d48.

  Definition FR : Z := 1856.
  Definition bofs : Z := 104.
  Definition cfg_slot : Z := 56.
  Definition err_slot : Z := 200.
  Definition alc_slot : Z := 1408.
  Definition lines_slot : Z := 72.
  Definition white_slot : Z := 1672.
  Definition out_size : Z := 208.

  Definition vf_vec_slots : list Z := [224; 256; 288; 320; 352; 384; 552; 424].
End LoTailAddr.
