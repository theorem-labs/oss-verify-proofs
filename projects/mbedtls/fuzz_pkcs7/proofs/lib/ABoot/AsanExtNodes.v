(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanExtNodes () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nil"].


Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.

(* [comment removed for export] *)
Fixpoint rom_bytes_ok (b : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_rom segs (Z_to_bv 64 b) with Some _ => rom_bytes_ok (b + 1) n' | None => false end
  end.

Definition node_imgword (cs : acs) (b : Z) (n : nat) : option acs :=
  if (fresh_ok nx0 cs && Nat.leb 1 n && Nat.leb n 8 && Z.leb 0 b && Z.ltb (b + 8) two64 && rom_bytes_ok b n)%bool
  then let v := nxt cs in
       let ss := a_ss cs in
       Some (with_ss cs (mk_ss (pc cs) (s_regs ss)
                              (KWord (SA (ELit 0) b) n (EVar v) :: kn_cutout (kn cs) (ELit 0) b (ELit (Z.of_nat n)))
                              (S v)))
  else None.

(* [comment removed for export] *)
Definition MSBMASK_WORDS : list Z := ltac2:(CDefT.buildp (gd_tbl_AsanExtNodes ()) "(0.$1.+155593.(0.$1.+55555637.(0.$1.+333336;7.(0.$1.+?0?1737.(0.$1.+10107;7.(0.$1.+;56533.(0.$1.+5556059;.(0.$1.+3336861;.(0.$1.+?0?7069;.(0.$1.+1017871;.(0.$1.+255793.(0.$1.+?56533.(0.$1.+2059793.(0.$1.+?585;3.(0.$1.+2061793.(0.$1.+?60633.(0.$1.+2069793.(0.$1.+?686;3.(0.$1.+2071793.(0.$1.+?70733.(0.$1.+455793.(0.$1.+?56533.(0.$1.+855793.(0.$1.+?56533.(0.$1.+1055793.(0.$1.+?56533.(0.$1.+2055793.(0.$1.+?56533.(0.$1.+???54513.(0.$1.+155793.(0.$1.+;7?5;3.(0.$1.+40;50533.(0.$1.+<575;3.(0.$1.+255513.(0.$1.+<57533.(0.$1.+:58533.(0.$1.+455593.(0.$1.+;50533.(0.$1.+=57533.(0.$1.+2>50533.(0.$1.+3855513.(0.$1.+40:0053;.(0.$1.+???00593.(0.$1.+:59533.(0.$1.+???54513.(2.$1.))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Fixpoint code_is (p : Z) (ws : list Z) : bool :=
  match ws with
  | [] => true
  | w :: ws' => match fetch_word segs (Z_to_bv 64 p) with
                | Some w' => Z.eqb (bv_unsigned w') w && code_is (p + 4) ws'
                | None => false
                end
  end.

Definition node_msbmask (cs : acs) : option acs :=
  let k := kn cs in let x := reg cs 10 in
  if (Z.leb 0 (pc cs) && Z.ltb (pc cs + 0xb8) two64 && code_is (pc cs) MSBMASK_WORDS
      && match xlo k x, xhi k x with
         | Some lo, Some hi => Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47)
         | _, _ => false
         end)%bool
  then let ss := a_ss cs in
       let sr := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs ss)
                   10 (ELit 0x7fffffffffff)) 11 (ELit 0xffffffffffffffff)) 12 (ELit 0x3333333333333333))
                   13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fffc00000000000) in
       Some (with_ss cs (mk_ss (pc cs + 0xb4) sr k (s_next ss)))
  else None.

(* [comment removed for export] *)
Definition XN_asan (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id, args with
  | 200%nat, [ELit b; ELit n] => node_imgword cs b (Z.to_nat n)
  | 202%nat, [] => node_msbmask cs
  | _, _ => None
  end.
End WithSegs.
