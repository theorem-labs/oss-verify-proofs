(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walks' instance hypothesis TL : PALib B (W_kit.v), proved for every B with
   AF0m.v's TfibSyms at the pinned placement PB_fr (W_img.v).  TfibSyms has no field for the shadow cell or its GOT
   slot; asyms_ok's aso_const_law (Reusable/YG0f.v) puts both cells in as_const B, and ts_const makes that list
   AF0m.v's Tfib_const, which has exactly one 8-byte cell holding SHADOW_OFF (at 0xa60b8, W_place.v's A_OBJ 32) and
   exactly one holding 0xa60b8 (at 0x9d9d0, A_OBJ 0).  The other fields are computations over ts_errno, ts_code
   (AF0l.v Tfib_code), ts_universe_drv (DRV_TRACES) and PB_fr. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG00 YG01 YG0f YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
AF0l AF0m W_syms W_listing W_tbl W_place W_kit W_img.
Import ListNotations.
Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

(* The addresses of the 8-byte constant cells of L that hold v. *)
Definition z8_addrs (v : Z) (L : list acell) : list Z :=
  flat_map (fun c => match c with
    | ACell (ANum a) w (AV (ANum v')) => if Nat.eqb w 8 && Z.eqb v' v then [a] else []
    | _ => [] end) L.
Lemma z8_addrs_in : forall a v L, In (z8 (ANum a) v) L -> In a (z8_addrs v L).
Proof.
intros a v L H. unfold z8_addrs. apply in_flat_map. exists (z8 (ANum a) v). split; [exact H|].
cbn. rewrite Z.eqb_refl. left. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma palib_tfib : forall B, TfibSyms B -> PALib (PI := PB_fr) B.
Proof.
intros B TS.
set (ly0 := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0)).
pose proof (@aso_const_law B (@ts_ok B TS) ly0) as (Kc & _ & Kg & _).
rewrite (@ts_const B TS ly0) in Kc, Kg.
(* the table's only 8-byte cell holding SHADOW_OFF, and its only one holding that cell's address *)
assert (Ac : z8_addrs SHADOW_OFF (Tfib_const ly0) = [0xa60b8]) by (vm_compute; reflexivity).
assert (Ag : z8_addrs 0xa60b8 (Tfib_const ly0) = [0x9d9d0]) by (vm_compute; reflexivity).
apply z8_addrs_in in Kc. rewrite Ac in Kc. destruct Kc as [Ec | []].
rewrite <- Ec in Kg. apply z8_addrs_in in Kg. rewrite Ag in Kg. destruct Kg as [Eg | []].
pose proof (@ts_code B TS) as Ecode. pose proof (@ts_errno B TS) as Eerr.
constructor.
- rewrite <- Eg. vm_compute. reflexivity.
- rewrite <- Ec. vm_compute. reflexivity.
- left. apply Z.leb_le. vm_compute. reflexivity.
- unfold api_env. rewrite Eerr, Ecode. split; [|split].
  + split; apply Z.leb_le; vm_compute; reflexivity.
  + intros a Ha. change (in_img frsegs a). unfold in_img. eexists. split; [right; right; right; left; reflexivity|].
    match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in
      let h := eval vm_compute in sz in change lo with l; change sz with h end.
    unfold TFIB_ERRNO in Ha. lia.
  + split; apply (@ts_universe_drv B TS); unfold DRV_TRACES.
    * do 7 right. left. reflexivity.
    * do 6 right. left. reflexivity.
- rewrite Ecode. vm_compute. reflexivity.
- rewrite Ecode. vm_compute. reflexivity.
- rewrite Ecode. split; apply Z.ltb_lt; vm_compute; reflexivity.
Qed.
End a.
