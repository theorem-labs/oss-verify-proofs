(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
#[using="Type"] Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Theorem afake_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts ->
  Forall (pfact_ok V) asan_pure_facts ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  ashadow1 V m ->      (* [comment removed for export] *)
  AFAKE (mkALayout (LV V) w U) [] m.
Proof.
  intros V w U m HM HP HAT SH1.
  set (L := mkALayout (LV V) w U).
  assert (EF : al_fake L = 4096 * V 393%nat) by reflexivity.
  assert (ED : al_dtls L = 4096 * V 310%nat) by reflexivity.
  assert (ET : al_t L = 4096 * V 227%nat) by reflexivity.
  (* [comment removed for export] *)
  pf V HP (PVar 393 1 34359733495) P393. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 65536) 6238208) DIh393. pf V HP (PVar 310 1 34359736319) P310. pf V HP (PVar 227 1 34359736319) P227.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 2147446784) 17592186048512) DB393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6238208) DI310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6238208) DI227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D3.
  (* [comment removed for export] *)
  mf V m HM (MCell (ZLit 6165936) 8 (ZLit 6166232)) C40. replace 6165936 with (ATPv + -8) in C40 by (rewrite ATPv_img; reflexivity). replace 6166232 with (ATPv + 288) in C40 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZLit 6165944) 8 (ZMul (ZLit 4096) (ZV 393))) C48. replace 6165944 with ATPv in C48 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZLit 6165952) 8 (ZMul (ZLit 4096) (ZV 310))) C70. replace 6165952 with (ATPv + 8) in C70 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZLit 6166240) 8 (ZLit 6167992)) C98. replace 6166240 with (ATPv + 296) in C98 by (rewrite ATPv_img; reflexivity). replace 6167992 with (ATPv + 2048) in C98 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6165944)) CD24. replace 6165944 with ATPv in CD24 by (rewrite ATPv_img; reflexivity).
  mf8 V m HM 0x1401b0 256 CCF.
  mf V m HM (MCell (ZLit 0x13e098) 4 (ZLit 0)) CVERB.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6167792)) CT48.      (* [comment removed for export] *)
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6168268)) CT56.
  mf V m HM (MZeroC (ZMul (ZLit 4096) (ZV 393)) 88) HINTS.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 393)) (ZLit 88)) 8 (ZLit 20)) CLOG.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 393)) (ZLit 96)) 11571104) Z96.
  pose proof (mwr_find asegs V m _ (ZMul (ZLit 4096) (ZV 393)) 11571200 HM ltac:(vm_compute; reflexivity)) as WFK. cbn [zv] in WFK.
  (* [comment removed for export] *)
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 208)) 137439023104) DR393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 228)) 65536) DC393.
  pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209. pf V HP (PVar 228 1 34359736304) P228.
  destruct (shadow_zero_run V m (512 * V 393%nat + 2147450880) 1446400 SH1 HM HP ltac:(lia)) as (ZSH & WSH & _).
  { intros a Ha. unfold ashadow. clear -Ha P393 DIh393 DB393 DW393 P0 P6 P10. lia. }
  { intros a Ha. unfold ASHOFF. clear -Ha P393 DIh393 DR393 DC393 P208 P209 P228. repeat split; intros X; Z.div_mod_to_equations; lia. }
  pose proof (mimg_cover asegs V m _ 0x10000 0xa73a0 HM ltac:(vm_compute; reflexivity)) as IMG.
  rewrite <- EF in *. rewrite <- ED in *. rewrite <- ET in *.
  assert (SHF : shad (al_fake L) = 512 * V 393%nat + 2147450880).
  { unfold shad, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2, EF by lia. change (2^3) with 8.
    replace (4096 * V 393%nat) with ((512 * V 393%nat) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (SHL : shlen FAKESZ = 1446400) by reflexivity.
  assert (G : afake_geom L).
  { unfold afake_geom, FAKESZ, ablk, sclr, iclr, KLS, AIMG_LO, AIMG_HI, tclr. rewrite EF, ED, ET in *. rewrite ATPv_img.
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ rewrite Z.mul_comm; apply Z_mod_mult
            | clear - P393 P0 P6 P10 DW393 DB393 DIh393 HAT; lia
            | clear - P310 P0 P6 P10 DW310 DB310 DI310 HAT; lia
            | clear - P227 P0 P6 P10 DW227 DB227 DI227 HAT; lia
            | clear - D1 D2 D3; lia ]. }
  clearbody L.
  split; [exact G|].
  split.
  { unfold afake_cells. split.
    { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xa7288 (le8 (Z_to_bv 64 0x9f398)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply IMG; rewrite length_le8 in Ha; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
    split; [apply (proj2 (rw_cells_app asegs m (ATPv + -8) [C8 _] [C8 _])); split; [exact C40| cbn [cells_size csize Nat.add]; replace (ATPv + -8 + Z.of_nat 8) with ATPv by (clear; lia); exact C48]|].
    split; [exact C70|]. split; [exact C98|]. split; [exact CD24|]. split.
    { assert (CF8 : rw_cells asegs m 1311152 ([C1 (Z_to_bv 8 0)] ++ ([C1 (Z_to_bv 8 1)] ++ [CB 6 (repeat (Z_to_bv 8 0) 6)]))).
      { eapply rw_cells_recast; [exact CCF| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. }
      apply (proj1 (rw_cells_app asegs m _ _ _)) in CF8 as [_ CF8]. cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.of_succ_nat] in CF8.
      apply (proj1 (rw_cells_app asegs m _ _ _)) in CF8 as [CF8 _]. exact CF8. }
    split; [exact CVERB|].
    apply (dc_of_cells m (al_t L + 48) [C8 (Z_to_bv 64 6167792); C8 (Z_to_bv 64 6168268)]).
    apply (proj2 (rw_cells_app asegs m _ [C8 _] [C8 _])). split; [exact CT48| cbn [cells_size csize Nat.add]].
    replace (al_t L + 48 + Z.of_nat 8) with (al_t L + 56) by lia. exact CT56. }
  split.
  { (* [comment removed for export] *)
    pose proof (dc_of_cells m _ _ HINTS) as D88. cbn [cells_size csize Nat.add] in D88. change (Z.of_nat (Z.to_nat 88)) with 88 in D88.
    destruct (dc_take m _ 88 8 D88 ltac:(lia)) as [D0 R0]. destruct (c8_of_dc m _ D0) as [h0 H0].
    destruct (dc_take m _ (88 - 8) 8 R0 ltac:(lia)) as [D1' R1]. destruct (c8_of_dc m _ D1') as [h1 H1].
    destruct (dc_take m _ (88 - 8 - 8) 8 R1 ltac:(lia)) as [D2' R2]. destruct (c8_of_dc m _ D2') as [h2 H2].
    destruct (dc_take m _ (88 - 8 - 8 - 8) 64 R2 ltac:(lia)) as [[hs HS] _]. change (Z.to_nat 64) with 64%nat in HS.
    exists h0, h1, h2, hs.
    apply (proj2 (rw_cells_app asegs m _ [C8 h0] _)). split; [exact H0| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app asegs m _ [C8 h1] _)). split; [replace (al_fake L + Z.of_nat 8) with (al_fake L + 8) by lia; exact H1| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app asegs m _ [C8 h2] _)). split; [replace (al_fake L + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8) by lia; exact H2| cbn [cells_size csize Nat.add]].
    replace (al_fake L + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8 + 8) by lia. exact HS. }
  split; [exact CLOG|].
  split.
  { eapply rw_cells_recast; [apply (mzero_rw_cells asegs m (al_fake L + 96) 1); [intros i Hi; apply Z96; lia| eapply wr_at_sub'; [exact WFK| lia| lia| lia]| lia]
      | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity]. }
  split.
  { exists (zeros (FAKESZ - 4096)). apply mzero_rw_cells; [| eapply wr_at_sub'; [exact WFK| lia| lia| unfold FAKESZ; lia]| unfold FAKESZ; lia].
    intros i Hi. replace (al_fake L + 4096 + i) with (al_fake L + 96 + (4000 + i)) by lia. apply Z96. unfold FAKESZ in Hi. lia. }
  split.
  { rewrite SHF, SHL. exists (zeros 1446400). apply mzero_rw_cells; [exact ZSH| exact WSH| lia]. }
  split.
  - intros c pos b Hc Hp Hb NZ. exfalso. apply NZ. pose proof (fk_flag_range L c pos Hc Hp) as R.
    specialize (Z96 (fk_flag L c pos - (al_fake L + 96)) ltac:(lia)). replace (al_fake L + 96 + (fk_flag L c pos - (al_fake L + 96))) with (fk_flag L c pos) in Z96 by lia.
    congruence.
  - intros c F n Hin. destruct Hin.
Qed.
End CANSEC2.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
#[using="Type"] Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Theorem afake_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok asegs V m) asan_mem_facts ->
  Forall (pfact_ok V) asan_pure_facts ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  ashadow1 V m ->      (* [comment removed for export] *)
  AFAKE (mkALayout (LV V) w U) [] m.
Proof.
  intros V w U m HM HP HAT SH1.
  set (L := mkALayout (LV V) w U).
  assert (EF : al_fake L = 4096 * V 393%nat) by reflexivity.
  assert (ED : al_dtls L = 4096 * V 310%nat) by reflexivity.
  assert (ET : al_t L = 4096 * V 227%nat) by reflexivity.
  (* [comment removed for export] *)
  pf V HP (PVar 393 1 34359733495) P393. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 65536) 6242304) DIh393. pf V HP (PVar 310 1 34359736319) P310. pf V HP (PVar 227 1 34359736319) P227.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 2147446784) 17592186048512) DB393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6242304) DI310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6242304) DI227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D3.
  (* [comment removed for export] *)
  mf V m HM (MCell (ZLit 6166960) 8 (ZLit 6167256)) C40. replace 6166960 with (ATPv + -8) in C40 by (rewrite ATPv_img; reflexivity). replace 6167256 with (ATPv + 288) in C40 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZLit 6166968) 8 (ZMul (ZLit 4096) (ZV 393))) C48. replace 6166968 with ATPv in C48 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZLit 6166976) 8 (ZMul (ZLit 4096) (ZV 310))) C70. replace 6166976 with (ATPv + 8) in C70 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZLit 6167264) 8 (ZLit 6169016)) C98. replace 6167264 with (ATPv + 296) in C98 by (rewrite ATPv_img; reflexivity). replace 6169016 with (ATPv + 2048) in C98 by (rewrite ATPv_img; reflexivity).
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6166968)) CD24. replace 6166968 with ATPv in CD24 by (rewrite ATPv_img; reflexivity).
  mf8 V m HM 0x1405b0 256 CCF.
  mf V m HM (MCell (ZLit 0x13e498) 4 (ZLit 0)) CVERB.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6168816)) CT48.      (* [comment removed for export] *)
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6169292)) CT56.
  mf V m HM (MZeroC (ZMul (ZLit 4096) (ZV 393)) 88) HINTS.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 393)) (ZLit 88)) 8 (ZLit 20)) CLOG.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 393)) (ZLit 96)) 11571104) Z96.
  pose proof (mwr_find asegs V m _ (ZMul (ZLit 4096) (ZV 393)) 11571200 HM ltac:(vm_compute; reflexivity)) as WFK. cbn [zv] in WFK.
  (* [comment removed for export] *)
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 208)) 137439023104) DR393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 228)) 65536) DC393.
  pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209. pf V HP (PVar 228 1 34359736304) P228.
  destruct (shadow_zero_run V m (512 * V 393%nat + 2147450880) 1446400 SH1 HM HP ltac:(lia)) as (ZSH & WSH & _).
  { intros a Ha. unfold ashadow. clear -Ha P393 DIh393 DB393 DW393 P0 P6 P10. lia. }
  { intros a Ha. unfold ASHOFF. clear -Ha P393 DIh393 DR393 DC393 P208 P209 P228. repeat split; intros X; Z.div_mod_to_equations; lia. }
  pose proof (mimg_cover asegs V m _ 0x10000 0xa7780 HM ltac:(vm_compute; reflexivity)) as IMG.
  rewrite <- EF in *. rewrite <- ED in *. rewrite <- ET in *.
  assert (SHF : shad (al_fake L) = 512 * V 393%nat + 2147450880).
  { unfold shad, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2, EF by lia. change (2^3) with 8.
    replace (4096 * V 393%nat) with ((512 * V 393%nat) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (SHL : shlen FAKESZ = 1446400) by reflexivity.
  assert (G : afake_geom L).
  { unfold afake_geom, FAKESZ, ablk, sclr, iclr, KLS, AIMG_LO, AIMG_HI, tclr. rewrite EF, ED, ET in *. rewrite ATPv_img.
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ rewrite Z.mul_comm; apply Z_mod_mult
            | clear - P393 P0 P6 P10 DW393 DB393 DIh393 HAT; lia
            | clear - P310 P0 P6 P10 DW310 DB310 DI310 HAT; lia
            | clear - P227 P0 P6 P10 DW227 DB227 DI227 HAT; lia
            | clear - D1 D2 D3; lia ]. }
  clearbody L.
  split; [exact G|].
  split.
  { unfold afake_cells. split.
    { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xa7668 (le8 (Z_to_bv 64 0x9f77c)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply IMG; rewrite length_le8 in Ha; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
    split; [apply (proj2 (rw_cells_app asegs m (ATPv + -8) [C8 _] [C8 _])); split; [exact C40| cbn [cells_size csize Nat.add]; replace (ATPv + -8 + Z.of_nat 8) with ATPv by (clear; lia); exact C48]|].
    split; [exact C70|]. split; [exact C98|]. split; [exact CD24|]. split.
    { assert (CF8 : rw_cells asegs m 1312176 ([C1 (Z_to_bv 8 0)] ++ ([C1 (Z_to_bv 8 1)] ++ [CB 6 (repeat (Z_to_bv 8 0) 6)]))).
      { eapply rw_cells_recast; [exact CCF| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. }
      apply (proj1 (rw_cells_app asegs m _ _ _)) in CF8 as [_ CF8]. cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.of_succ_nat] in CF8.
      apply (proj1 (rw_cells_app asegs m _ _ _)) in CF8 as [CF8 _]. exact CF8. }
    split; [exact CVERB|].
    apply (dc_of_cells m (al_t L + 48) [C8 (Z_to_bv 64 6168816); C8 (Z_to_bv 64 6169292)]).
    apply (proj2 (rw_cells_app asegs m _ [C8 _] [C8 _])). split; [exact CT48| cbn [cells_size csize Nat.add]].
    replace (al_t L + 48 + Z.of_nat 8) with (al_t L + 56) by lia. exact CT56. }
  split.
  { (* [comment removed for export] *)
    pose proof (dc_of_cells m _ _ HINTS) as D88. cbn [cells_size csize Nat.add] in D88. change (Z.of_nat (Z.to_nat 88)) with 88 in D88.
    destruct (dc_take m _ 88 8 D88 ltac:(lia)) as [D0 R0]. destruct (c8_of_dc m _ D0) as [h0 H0].
    destruct (dc_take m _ (88 - 8) 8 R0 ltac:(lia)) as [D1' R1]. destruct (c8_of_dc m _ D1') as [h1 H1].
    destruct (dc_take m _ (88 - 8 - 8) 8 R1 ltac:(lia)) as [D2' R2]. destruct (c8_of_dc m _ D2') as [h2 H2].
    destruct (dc_take m _ (88 - 8 - 8 - 8) 64 R2 ltac:(lia)) as [[hs HS] _]. change (Z.to_nat 64) with 64%nat in HS.
    exists h0, h1, h2, hs.
    apply (proj2 (rw_cells_app asegs m _ [C8 h0] _)). split; [exact H0| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app asegs m _ [C8 h1] _)). split; [replace (al_fake L + Z.of_nat 8) with (al_fake L + 8) by lia; exact H1| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app asegs m _ [C8 h2] _)). split; [replace (al_fake L + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8) by lia; exact H2| cbn [cells_size csize Nat.add]].
    replace (al_fake L + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8 + 8) by lia. exact HS. }
  split; [exact CLOG|].
  split.
  { eapply rw_cells_recast; [apply (mzero_rw_cells asegs m (al_fake L + 96) 1); [intros i Hi; apply Z96; lia| eapply wr_at_sub'; [exact WFK| lia| lia| lia]| lia]
      | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity]. }
  split.
  { exists (zeros (FAKESZ - 4096)). apply mzero_rw_cells; [| eapply wr_at_sub'; [exact WFK| lia| lia| unfold FAKESZ; lia]| unfold FAKESZ; lia].
    intros i Hi. replace (al_fake L + 4096 + i) with (al_fake L + 96 + (4000 + i)) by lia. apply Z96. unfold FAKESZ in Hi. lia. }
  split.
  { rewrite SHF, SHL. exists (zeros 1446400). apply mzero_rw_cells; [exact ZSH| exact WSH| lia]. }
  split.
  - intros c pos b Hc Hp Hb NZ. exfalso. apply NZ. pose proof (fk_flag_range L c pos Hc Hp) as R.
    specialize (Z96 (fk_flag L c pos - (al_fake L + 96)) ltac:(lia)). replace (al_fake L + 96 + (fk_flag L c pos - (al_fake L + 96))) with (fk_flag L c pos) in Z96 by lia.
    congruence.
  - intros c F n Hin. destruct Hin.
Qed.
End CANSEC2.
End TwB.
