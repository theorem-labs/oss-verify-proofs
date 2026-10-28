(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Lemma huf_type_readA : forall (dtb : list byte) ty, nth_error dtb 1 = Some ty ->
  extz false 1 (bytes_le_to_Z (firstn 1 (skipn (Z.to_nat 1) dtb))) = bv_unsigned ty.
Proof.
  intros dtb ty H. change (Z.to_nat 1) with 1%nat.
  destruct dtb as [|x0 [|x1 r]]; cbn in H; try discriminate. injection H as ->.
  cbn [skipn firstn]. unfold extz. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma aappW_frame16 : forall SPV, KHIGH <= SPV - 16 -> aappW [(SPV - 16, SPV)].
Proof. intros SPV H. constructor; [cbn [fst snd]; right; exact H | constructor]. Qed.

Lemma unpoisoned_frame16 : forall m m' SPV A B, unpoisoned m A B -> munch [(SPV - 16, SPV)] m m' -> KHIGH <= SPV - 16 ->
  0 <= A -> B <= KEND -> unpoisoned m' A B.
Proof.
  intros m m' SPV A B U MU K HA HB.
  eapply unpoisoned_munch; [exact U | exact MU |]. cbn [disjoint_from fst snd]. split; [|exact I].
  rewrite !shad_div. unfold ASHOFF, KHIGH, KEND in *. left. Z.div_mod_to_equations. lia.
Qed.

Lemma areg_frame16 : forall RNG m m' SPV A n, areg RNG m A n -> munch [(SPV - 16, SPV)] m m' -> KHIGH <= SPV - 16 -> areg RNG m' A n.
Proof.
  intros RNG m m' SPV A n H MU K Hn. destruct (H Hn) as (AB & U & R & RS).
  split; [exact AB | split; [| split; [exact R | exact RS]]].
  pose proof (ablk_lin _ _ AB) as (? & ? & ? & ?).
  eapply unpoisoned_frame16; [exact U | exact MU | exact K | lia | unfold KEND; lia].
Qed.

Lemma aro_frame16 : forall RNG m m' SPV A n, aro RNG m A n -> munch [(SPV - 16, SPV)] m m' -> KHIGH <= SPV - 16 ->
  0 <= A -> A + n <= KEND -> aro RNG m' A n.
Proof.
  intros RNG m m' SPV A n (U & R & RS) MU K HA HB. split; [| split; [exact R | exact RS]].
  eapply unpoisoned_frame16; eassumption.
Qed.

Lemma disjoint_from_above16 : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  intros W A n K HW LE. induction HW as [|[x y] W Hx HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst] in Hx. split; [lia | exact IH].
Qed.

Lemma art_frame16 : forall m m' SPV, art m -> munch [(SPV - 16, SPV)] m m' -> wmono bsegs m m' -> KHIGH <= SPV - 16 -> art m'.
Proof.
  intros m m' SPV (GOT & RIC & SHB & INI & LAY & REAL) MU WM K.
  assert (HW : Forall (fun iv : Z * Z => 0xd1740 <= fst iv) [(SPV - 16, SPV)])
    by (constructor; [cbn [fst]; unfold KHIGH in K; lia | constructor]).
  unfold art. split; [|split; [|split; [|split; [|split]]]].
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_above16; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_above16; [exact HW| cbn; lia]] ].
Qed.

Ltac and_spine := lazymatch goal with |- _ /\ _ => split; [| and_spine] | _ => idtac end.

Lemma huf_dec_preA_frame16 : forall RNG m m' SPV lo fr fr' DST dcap SRC n src,
  huf_dec_preA RNG m SPV lo fr DST dcap SRC n src -> 16 <= fr' <= fr ->
  munch [(SPV - 16, SPV)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  stk bsegs m' lo SPV -> stk bsegs m' DST (DST + dcap) ->
  huf_dec_preA RNG m' SPV lo fr' DST dcap SRC n src.
Proof.
  intros RNG m m' SPV lo fr fr' DST dcap SRC n src
    (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SRCL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & AD & AS & ART & ASTK & AZ & ARO & SPA)
    HF MU WM MI' STK' OUT'.
  pose proof ASTK as (KLO & _ & _).
  assert (K : KHIGH <= SPV - 16) by lia.
  unfold huf_dec_preA. and_spine.
  all: first [ eassumption
             | eapply bytes_at_transport; [exact SRCB | exact MU | cbn [disjoint_from fst snd]; lia]
             | eapply areg_frame16; [eassumption | exact MU | exact K]
             | eapply art_frame16; [exact ART | exact MU | exact WM | exact K]
             | eapply azstk_transport; [exact AZ | exact MU | exact WM | apply aappW_frame16; exact K | lia]
             | eapply aro_client_transport; [exact ARO | exact MU | exact WM | apply aappW_frame16; exact K]
             | lia ].
Qed.

Lemma huf_dt_preA_frame16 : forall RNG m m' SPV lo DST dcap DT dtb,
  huf_dt_preA RNG m SPV lo DST dcap DT dtb -> KHIGH <= lo -> lo <= SPV - 16 ->
  munch [(SPV - 16, SPV)] m m' -> huf_dt_preA RNG m' SPV lo DST dcap DT dtb.
Proof.
  intros RNG m m' SPV lo DST dcap DT dtb (DTB & DL & T0 & T1 & OS3 & DJ2 & ARO & DTA) K LO MU.
  unfold huf_dt_preA, HUF_DTABLE_BYTES in *. and_spine.
  all: first [ eassumption
             | eapply bytes_at_transport; [exact DTB | exact MU | cbn [disjoint_from fst snd]; lia]
             | eapply aro_frame16; [exact ARO | exact MU | lia | lia | unfold KEND; lia]
             | lia ].
Qed.

(* [comment removed for export] *)
Ltac huf_dispA_tac T1 T2 H1 H2 :=
  let PRE := fresh "PRE" in let DTP := fresh "DTP" in let TOK := fresh "TOK" in
  intros PRE DTP TOK;
  let PRE' := fresh "PRE'" in let DTP' := fresh "DTP'" in
  pose proof PRE as PRE'; pose proof DTP as DTP';
  let MI := fresh "MI" in let STK := fresh "STK" in let ART := fresh "ART" in let ASTK := fresh "ASTK" in
  destruct PRE' as (MI & STK & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ART & ASTK & ? & ? & ?);
  let DTB := fresh "DTB" in let ARO := fresh "ARO" in
  let DTA := fresh "DTA" in
  destruct DTP' as (DTB & ? & ? & ? & ? & ? & ARO & DTA);
  let HDR := fresh "HDR" in let ty := fresh "ty" in let tl := fresh "tl" in let TY := fresh "TY" in
  let TLB := fresh "TLB" in let TLR := fresh "TLR" in let X2 := fresh "X2" in let NB := fresh "NB" in
  pose proof TOK as (HDR & ty & tl & TY & TLB & TLR & X2 & NB);
  unfold HUF_DTABLE_BYTES in *;
  let GOT := fresh "GOT" in let SHB := fresh "SHB" in
  pose proof ART as (GOT & ? & SHB & ? & ? & ?);
  let KLO := fresh "KLO" in let RSTK := fresh "RSTK" in
  pose proof ASTK as (KLO & RSTK & ?); unfold KHIGH in KLO;
  let UDT := fresh "UDT" in let RDT := fresh "RDT" in let RDTS := fresh "RDTS" in
  pose proof ARO as (UDT & RDT & RDTS);
  pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS (mkR _ (Z_to_bv 64 ?SPV) _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?DT) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?m _) =>
      let MU := fresh "MU" in let WM := fresh "WM" in
      assert (MU : munch [(SPV - 16, SPV)] m m) by apply munch_refl;
      assert (WM : wmono bsegs m m) by apply wmono_refl;
      let STK2 := fresh "STK2" in pose proof STK as STK2;
      carve_frame 16%nat STK2;
      assert (RSTKf : rng RNG (SPV - 16) 16) by (eapply rng_sub; [exact RSTK | lia | lia]);
      pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDT ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; lia)) as UDTz;
      kx_autoFLA (GOT, SHB) [KAUnp DT 16388; KAApp (SPV - 16) 16] [T1; T2] 40%nat
        [KZRange DT 4096 (2^47 - 16388); KZAlign DT 4; KZRange SPV 0x10007fff8000 (2^47); KZWr (SPV - 16) 16; KZDisj (SPV - 16) 16 DT 16388]
        [(DT, 16388); (SPV - 16, 16)] [(DT, 16388); (SPV - 16, 16)];
      [ try kx_cell_lit; try kx_z; try match goal with H : rng _ 65536 _ |- accP _ _ _ => kx_acc H end .. ];
      [ (let RD := fresh "RD" in
         lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?r15 ?r16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           first [ lazymatch r15 with ev _ ?k => kx_read_eq k RD end | lazymatch r16 with ev _ ?k => kx_read_eq k RD end ] end;
         rewrite (rdval_bytes_at bsegs _ DT _ 1 1 false DTB ltac:(lia) ltac:(change (Z.to_nat 1) with 1%nat; lia)), (huf_type_readA _ ty TY) in RD;
         rewrite RD in *; clear RD;
         rewrite Z_to_bv_unsigned, bv_wrap_small in *
           by (pose proof (bv_unsigned_in_range 8 ty) as RB; unfold bv_modulus in *; change (2 ^ Z.of_N 8) with 256 in RB;
               change (2 ^ Z.of_N 64) with (2^64); lia);
         kx_mem;
         lazymatch goal with FRx : rw_cells bsegs ?mm (SPV + -16) _, STx : stk bsegs ?mm _ (SPV + -16) |- _ => release_frame FRx STx SPV end;
         eapply evtF_mono;
         [ first [ eapply H2; [ eapply huf_dec_preA_frame16; [exact PRE | lia | exact MU | exact WM | assumption | assumption | assumption]
                              | eapply huf_dt_preA_frame16; [exact DTP | unfold KHIGH; lia | lia | exact MU]
                              | exact TLB | exact TLR | intros _; apply X2; assumption
                              | match goal with K : bv_unsigned ty <> 0 |- _ => apply Z.eqb_neq in K; rewrite K in NB end; exact NB ]
                 | eapply H1; [ eapply huf_dec_preA_frame16; [exact PRE | lia | exact MU | exact WM | assumption | assumption | assumption]
                              | eapply huf_dt_preA_frame16; [exact DTP | unfold KHIGH; lia | lia | exact MU]
                              | exact TLB | exact TLR | let X := fresh "X" in intro X; discriminate X
                              | match goal with K : bv_unsigned ty = 0 |- _ => rewrite K in NB end; exact NB ] ]
         | let ms' := fresh "ms'" in let P := fresh "P" in
           intros ms' P; unfold huf_dec_postA in *;
           let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
           destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU2 & WM2 & ? & ? & ? & ? & ? & ?);
           repeat (lazymatch goal with |- ex _ => eexists end);
           split; [reflexivity|];
           split; [ eapply munch_trans; [ eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside fst snd app]; intros; lia
                                        | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside fst snd app]; intros; lia ]
                  | ];
           split; [ eapply wmono_trans; [exact WM | exact WM2] |];
           repeat (split; [assumption|]); assumption ]) .. ]
  end.

Theorem huf_1x_proofA : huf_1x1_stmtA -> huf_1x2_stmtA -> huf_1x_stmtA.
Proof.
  intros H1 H2. unfold huf_1x_stmtA, huf_using_stmtA_at, APHUF_1X.
  unfold huf_1x1_stmtA, huf_1x2_stmtA, huf_int_stmtA_at, APHUF_1X1, APHUF_1X2 in *.
  intros until dtb. huf_dispA_tac 0x9b088 0x99a40 H1 H2.
Qed.

Theorem huf_4x_proofA : huf_4x1_stmtA -> huf_4x2_stmtA -> huf_4x_stmtA.
Proof.
  intros H1 H2. unfold huf_4x_stmtA, huf_using_stmtA_at, APHUF_4X.
  unfold huf_4x1_stmtA, huf_4x2_stmtA, huf_int_stmtA_at, APHUF_4X1, APHUF_4X2 in *.
  intros until dtb. huf_dispA_tac 0xa4cbc 0x9bb00 H1 H2.
Qed.
End CANSEC1.
