(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u.
From Stdlib Require Import Classical.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TK2.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Section Xfer.
Variable K : Z -> Prop.
Variables M M' : mem.
Hypothesis AG : TK.samem K M M'.
Definition cov (a n : Z) : Prop := forall i, a <= i < a + n -> K i.

Lemma u8_x : forall a v, 0 <= a < 2 ^ 62 -> cov a 1 -> PML.u8 M a v -> PML.u8 M' a v.
Proof. intros a v Ha HK H. apply (TK.u8_samem K M M' a v AG); [lia | apply HK; lia | exact H]. Qed.
Lemma u32_x : forall a v, 0 <= a < 2 ^ 62 -> cov a 4 -> PML.u32 M a v -> PML.u32 M' a v.
Proof. intros a v Ha HK H. apply (TK.u32_samem K M M' a v AG); [lia | exact HK | exact H]. Qed.
Lemma u64_x : forall a v, 0 <= a < 2 ^ 62 -> cov a 8 -> PML.u64 M a v -> PML.u64 M' a v.
Proof. intros a v Ha HK H. apply (TK.u64_samem K M M' a v AG); [lia | exact HK | exact H]. Qed.
Lemma cov_sub : forall a n a' n', cov a n -> a <= a' -> a' + n' <= a + n -> cov a' n'.
Proof. intros a n a' n' H H1 H2 i Hi. apply H. lia. Qed.

Lemma lstr_short_x : forall o s, 0 <= o < 2 ^ 62 -> cov o 24 -> L5.lstr_short RSEGS M o s -> L5.lstr_short RSEGS M' o s.
Proof.
  intros o s Ho HK (Hl & H0 & Hb & Hn). split; [exact Hl|]. split; [|split].
  - apply (TK.u8_samem K M M' _ _ AG); [lia | apply HK; lia | exact H0].
  - apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply HK; lia | exact Hb].
  - apply (TK.u8_samem K M M' _ _ AG); [lia | apply HK; lia | exact Hn].
Qed.
Lemma lstr_long_x : forall o s w0 p, 0 <= o < 2 ^ 62 -> 0 <= p -> p + Z.of_nat (length s) + 1 < 2 ^ 62 -> cov o 24 -> cov p (Z.of_nat (length s) + 1) ->
  L5.lstr_long RSEGS M o s w0 p -> L5.lstr_long RSEGS M' o s w0 p.
Proof.
  intros o s w0 p Ho Hp Hp2 HK HKp (Hb & H0 & H8 & H16 & Hbs & Hn). split; [exact Hb|]. split; [|split; [|split; [|split]]].
  - apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact H0].
  - apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact H8].
  - apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact H16].
  - apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply HKp; lia | exact Hbs].
  - apply (TK.u8_samem K M M' _ _ AG); [lia | apply HKp; lia | exact Hn].
Qed.

Definition str_cov (o : Z) (r : PML.srep) : Prop :=
  cov o 24 /\ match r with PML.SShort _ => True | PML.SLong cap p s => 0 <= p /\ p + cap < 2 ^ 62 /\ cov p cap end.
Lemma str_at_w_x : forall o r, 0 <= o < 2 ^ 62 -> str_cov o r -> PML.str_at_w M o r -> PML.str_at_w M' o r.
Proof.
  intros o r Ho [HK HB] H. destruct r as [s | cap p s]; cbn [PML.str_at_w] in *.
  - apply lstr_short_x; assumption.
  - destruct H as [H Hlt]. destruct HB as (Hp & Hpc & HKp). split; [|exact Hlt].
    apply lstr_long_x; [lia | lia | lia | exact HK | eapply cov_sub; [exact HKp | lia | lia] | exact H].
Qed.
Lemma str_at_x : forall o r, 0 <= o < 2 ^ 62 -> str_cov o r -> PML.str_at M o r -> PML.str_at M' o r.
Proof.
  intros o r Ho [HK HB] H. destruct r as [s | cap p s]; cbn [PML.str_at] in *.
  - apply lstr_short_x; assumption.
  - destruct H as (H & H8 & Hlt). destruct HB as (Hp & Hpc & HKp). split; [|split; [exact H8 | exact Hlt]].
    apply lstr_long_x; [lia | lia | lia | exact HK | eapply cov_sub; [exact HKp | lia | lia] | exact H].
Qed.

Lemma vis_at_x : forall V, 0 <= V < 2 ^ 62 -> cov V 48 -> PML.vis_at M V -> PML.vis_at M' V.
Proof. intros V HV HK (H & Hd). split; [apply u64_x; [exact HV | eapply cov_sub; [exact HK | lia | lia] | exact H] | apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Hd]]. Qed.
Lemma ec_at_x : forall E code, 0 <= E < 2 ^ 61 -> cov E 16 -> PML.ec_at M E code -> PML.ec_at M' E code.
Proof.
  intros E code HE HK (H0 & Hd & Hc). split; [|split].
  - apply u32_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H0].
  - apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Hd].
  - destruct Hc as [Hc | [Hc H8]]; [left; exact Hc | right; split; [exact Hc|]]. apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H8].
Qed.
Lemma iosb_at_x : forall B rd rb, 0 <= B < 2 ^ 61 -> cov B 152 -> PML.iosb_at M B rd rb -> PML.iosb_at M' B rd rb.
Proof.
  intros B rd rb HB HK (H32 & H36 & H40 & H48 & Hk & Hd).
  split; [apply u32_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H32]|].
  split; [apply u32_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H36]|].
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H40]|].
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H48]|].
  split; [intros k Hk0; apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact (Hk k Hk0)]|].
  apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Hd].
Qed.
Lemma isrc_at_x : forall IS rep g rd, 0 <= IS < 2 ^ 60 -> cov IS 272 -> str_cov (IS + 80) rep -> PML.isrc_at M IS rep g rd -> PML.isrc_at M' IS rep g rd.
Proof.
  intros IS rep g rd HIS HK HS H. unfold PML.isrc_at in *. cbv zeta in *.
  destruct H as (A0 & A16 & A24 & A32 & A40 & A48 & Ag & A56 & A64 & A72 & As & A104 & A112 & A120 & Aio & Ard & Adef).
  assert (C8 : forall off, 0 <= off -> off + 8 <= 272 -> cov (IS + off) 8) by (intros off H1 H2; eapply cov_sub; [exact HK | lia | lia]).
  repeat (split; [first [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] | assumption]|]).
  split; [apply str_at_x; [lia | exact HS | exact As]|].
  split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|].
  split; [apply u32_x; [lia | eapply cov_sub; [exact HK | lia | lia] | assumption]|].
  split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|].
  split; [apply iosb_at_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact Aio]|].
  split; [exact Ard|]. apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Adef].
Qed.

Definition ps_cov (ps : PML.pstate) : Prop :=
  0 <= PML.ps_bptr ps /\ PML.ps_bptr ps + PML.ps_bcap ps < 2 ^ 62 /\ cov (PML.ps_bptr ps) (PML.ps_bcap ps) /\
  0 <= PML.ps_sb ps /\ PML.ps_sb ps + PML.ps_scap ps < 2 ^ 62 /\ cov (PML.ps_sb ps) (PML.ps_scap ps).
Lemma parser_at_x : forall P ps, 0 <= P < 2 ^ 60 -> cov P 272 -> ps_cov ps -> PML.parser_at M P ps -> PML.parser_at M' P ps.
Proof.
  intros P ps HP HK (B1 & B2 & B3 & S1 & S2 & S3) H. unfold PML.parser_at in *.
  assert (C8 : forall off, 0 <= off -> off + 8 <= 272 -> cov (P + off) 8) by (intros off H1 H2; eapply cov_sub; [exact HK | lia | lia]).
  assert (C4 : forall off, 0 <= off -> off + 4 <= 272 -> cov (P + off) 4) by (intros off H1 H2; eapply cov_sub; [exact HK | lia | lia]).
  assert (C1 : forall off, 0 <= off -> off + 1 <= 272 -> cov (P + off) 1) by (intros off H1 H2; eapply cov_sub; [exact HK | lia | lia]).
  assert (C24 : forall off, 0 <= off -> off + 24 <= 272 -> cov (P + off) 24) by (intros off H1 H2; eapply cov_sub; [exact HK | lia | lia]).
  destruct H as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  repeat (split; [first [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] | apply u32_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] | apply u8_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]
                        | apply lstr_short_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] ]|]).
  split.
  { destruct (PML.ps_win ps) as [[p e]|]; [destruct Aw as (W1 & W2 & W3) | destruct Aw as (W1 & W2)]; repeat split; try assumption; apply u64_x; try assumption; try lia; (eapply cov_sub; [exact HK | lia | lia]). }
  repeat (split; [first [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] | apply u32_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] | apply u8_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]]|]).
  split; [apply str_at_x; [lia | split; [(eapply cov_sub; [exact HK | lia | lia]) | split; [exact B1 | split; [exact B2 | exact B3]]] | exact Abuf]|].
  split; [exact Abc|].
  repeat (split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|]).
  split; [apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply S3; lia | exact Astk]|].
  split; [exact Asl|]. apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Adef].
Qed.
Lemma source_at_x : forall R ch, 0 <= R < 2 ^ 60 -> cov R 320 -> PML.source_at M R ch -> PML.source_at M' R ch.
Proof.
  intros R ch HR HK (A264 & A272 & (st0 & Aio) & A32 & Adef).
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact A264]|].
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact A272]|].
  split; [exists st0; apply iosb_at_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact Aio]|].
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact A32]|].
  apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Adef].
Qed.
Lemma reader_at_x : forall R IS V ch bof ps, 0 <= R < 2 ^ 59 -> cov R 592 -> ps_cov ps -> PML.ps_win ps = None ->
  PML.reader_at M R IS V ch bof ps -> PML.reader_at M' R IS V ch bof ps.
Proof.
  intros R IS V ch bof ps HR HK HPS Hwin H. unfold PML.reader_at in *.
  assert (C8 : forall off, 0 <= off -> off + 8 <= 592 -> cov (R + off) 8) by (intros off H1 H2; eapply cov_sub; [exact HK | lia | lia]).
  destruct H as (A240 & A248 & A264 & A272 & (de & A280 & Hde) & A288 & A296 & A304 & A312 & (st0 & Aio) & A32 & Apar & Awin & Adef).
  repeat (split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|]).
  split; [exists de; split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption] | exact Hde]|].
  split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|].
  split; [apply u8_x; [lia | eapply cov_sub; [exact HK | lia | lia] | assumption]|].
  repeat (split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|]).
  split; [exists st0; apply iosb_at_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact Aio]|].
  split; [apply u64_x; [lia | (eapply cov_sub; [exact HK | lia | lia]) | assumption]|].
  split; [apply parser_at_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact HPS | exact Apar]|].
  split; [rewrite Hwin; exact I|]. apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Adef].
Qed.

Lemma iosb_at_xg : forall B rd rb, 0 <= B < 2 ^ 61 -> cov (B + 32) 120 -> mem_grows M M' -> PML.iosb_at M B rd rb -> PML.iosb_at M' B rd rb.
Proof.
  intros B rd rb HB HK MG (H32 & H36 & H40 & H48 & Hk & Hd).
  split; [apply u32_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H32]|].
  split; [apply u32_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H36]|].
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H40]|].
  split; [apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact H48]|].
  split; [intros k Hk0; apply u64_x; [lia | eapply cov_sub; [exact HK | lia | lia] | exact (Hk k Hk0)]|].
  exact (L5.defined_grows M M' _ _ MG Hd).
Qed.

Definition statics_cov : Prop := (forall a, PML.in_foot11 a -> K a) /\ (forall a, 0x10000 <= a < PML.IMG_RO_HI -> K a) /\ (forall a, 0xf6a93 <= a < 0xf6a94 \/ 0xf6b68 <= a < 0xf6b6c -> K a).
Lemma in_foot11_iv : forall lo hi a, In (lo, hi) PML.ll_foot_csrc -> lo <= a < hi -> PML.in_foot11 a.
Proof. intros lo hi a Hin Ha. exists (lo, hi). split; [exact Hin | exact Ha]. Qed.
Lemma img_ro_x : statics_cov -> PML.img_ro M -> PML.img_ro M'.
Proof. intros [_ [HR _]] H. apply (TK.img_clear_samem K M M' _ _ AG); [lia | unfold PML.IMG_RO_HI; lia | exact HR | exact H]. Qed.
Lemma libc_quiet_x : statics_cov -> PML.libc_quiet M -> PML.libc_quiet M'.
Proof.
  intros [_ [_ HQ]] [Q1 Q2]. unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK in *.
  split; [apply u8_x; [lia | intros i Hi; apply HQ; lia | exact Q1] | apply u32_x; [lia | intros i Hi; apply HQ; lia | exact Q2]].
Qed.

Ltac foot_cell :=
  lazymatch goal with
  | |- PML.in_foot11 ?a =>
      first [ apply (in_foot11_iv 0xd4df0 0xd4df2); [cbn; tauto | lia] | apply (in_foot11_iv 0xd4df8 0xd4dfa); [cbn; tauto | lia] | apply (in_foot11_iv 0xd5030 0xd5032); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd5040 0xd5238); [cbn; tauto | lia] | apply (in_foot11_iv 0xd52e8 0xd5768); [cbn; tauto | lia]
            | apply (in_foot11_iv 0xd5e98 0xd5ef8); [cbn; tauto | lia] | apply (in_foot11_iv 0xf6848 0xf6a68); [cbn; tauto | lia] ]
  end.
Section Statics.
Hypothesis SC : statics_cov.
Ltac sc_cell := first [ apply u8_x; [lia | intros i Hi; apply (proj1 SC); foot_cell | assumption]
                      | apply u32_x; [lia | intros i Hi; apply (proj1 SC); foot_cell | assumption]
                      | apply u64_x; [lia | intros i Hi; apply (proj1 SC); foot_cell | assumption] ].
Lemma loc_done_x : PML.loc_done M -> PML.loc_done M'.
Proof. intros (A & B & C). unfold PML.loc_done. repeat split; sc_cell. Qed.
Lemma gloc_done_x : PMS.gloc_done M -> PMS.gloc_done M'.
Proof. intros (A & B). unfold PMS.gloc_done. repeat split; sc_cell. Qed.
Lemma errcat_x : forall b, PML.errcat_guard M b -> PML.errcat_guard M' b.
Proof. intros b (A & B). unfold PML.errcat_guard. split; sc_cell. Qed.
Lemma convcat_x : forall b, PML.convcat_guard M b -> PML.convcat_guard M' b.
Proof. intros b (A & B). unfold PML.convcat_guard. split; sc_cell. Qed.
Lemma atexit_cells_x : forall hs, PML.atexit_cells M hs -> PML.atexit_cells M' hs.
Proof.
  intros hs (A & B & C & D & E & F & G & H). unfold PML.atexit_cells, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD in *.
  split; [sc_cell|]. split; [sc_cell|]. split; [sc_cell|]. split; [sc_cell|]. split; [sc_cell|]. split; [sc_cell|]. split; [sc_cell|].
  destruct hs as [|[f a] [|[f2 a2] [|h3 hs]]]; [exact I | | | exact H].
  - destruct H as (H1 & H2). split; sc_cell.
  - destruct H as (H1 & H2 & H3 & H4). split; [sc_cell|]. split; [sc_cell|]. split; sc_cell.
Qed.
Lemma ls_ok_x : forall g, PML.ls_ok g M -> PML.ls_ok g M'.
Proof.
  intros g (RO & LQ & OK). split; [exact (img_ro_x SC RO)|]. split; [exact (libc_quiet_x SC LQ)|]. destruct g.
  -
    destruct OK as (FP & AC0). split; [| exact (atexit_cells_x _ AC0)].
    intros a Hin. assert (Ha : 0 <= a < 2 ^ 64).
    { destruct Hin as (iv & Hiv & Hr). unfold PML.ll_prist_csrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn in Hr; lia|]). destruct Hiv. }
    rewrite (AG a Ha (proj1 SC a (PML.in_prist_foot11 a Hin))). apply FP. exact Hin.
  - destruct OK as (A & B & C & D). split; [exact (loc_done_x A)|]. split; [exact (errcat_x _ B)|]. split; [exact (convcat_x _ C) | exact (atexit_cells_x _ D)].
  - destruct OK as (A & B & C & D). split; [exact (loc_done_x A)|]. split; [exact (errcat_x _ B)|]. split; [exact (convcat_x _ C) | exact (atexit_cells_x _ D)].
  - destruct OK as (A & B & C & D). split; [exact (loc_done_x A)|]. split; [exact (errcat_x _ B)|]. split; [exact (convcat_x _ C) | exact (atexit_cells_x _ D)].
  - destruct OK as (A & B & C & D). split; [exact (loc_done_x A)|]. split; [exact (errcat_x _ B)|]. split; [exact (convcat_x _ C) | exact (atexit_cells_x _ D)].
  - destruct OK as (A & B & C & D). split; [exact (loc_done_x A)|]. split; [exact (errcat_x _ B)|]. split; [exact (convcat_x _ C) | exact (atexit_cells_x _ D)].
Qed.
Lemma statics_mid_x : PMS.statics_mid M -> PMS.statics_mid M'.
Proof.
  intros (RO & LQ & GL & SG & EC). split; [exact (img_ro_x SC RO)|]. split; [exact (libc_quiet_x SC LQ)|]. split; [exact (gloc_done_x GL)|]. split.
  - destruct SG as [[A B]|A]; [left; split; sc_cell | right; sc_cell].
  - destruct EC as (g & Hg & A & B & C). exists g. split; [exact Hg|]. split; [exact (errcat_x _ A)|]. split; [exact (convcat_x _ B) | exact (atexit_cells_x _ C)].
Qed.
End Statics.

Lemma mid_to_ls : (forall a, PML.in_foot11 a -> ~ (0xd5030 <= a < 0xd5032) -> K a) -> (forall a, 0x10000 <= a < PML.IMG_RO_HI \/ 0xf6a93 <= a < 0xf6a94 \/ 0xf6b68 <= a < 0xf6b6c -> K a) ->
  PMS.statics_mid M -> PML.u8 M' 0xd5030 1 -> exists g', g' <> PML.LS0 /\ PML.ls_ok g' M'.
Proof.
  intros KF KR (RO & (Q1 & Q2) & (G1 & G2) & _ & EC) GD.
  assert (RO' : PML.img_ro M') by (apply (TK.img_clear_samem K M M' _ _ AG); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; apply KR; left; exact Hi | exact RO]).
  assert (LQ' : PML.libc_quiet M').
  { unfold PML.libc_quiet, PML.NEED_LOCKS, PML.LOCALE_LOCK in *. split; [apply u8_x; [lia | intros i Hi; apply KR; lia | exact Q1] | apply u32_x; [lia | intros i Hi; apply KR; lia | exact Q2]]. }
  assert (F : forall a n, 0xd4df8 <= a -> a + n <= 0xd5030 \/ (0xd5032 <= a /\ 0xd5040 <= a) -> (PML.in_foot11 a -> True) -> True) by (intros; exact I). clear F.
  assert (X8 : forall a v, PML.u8 M a v -> 0 <= a < 2 ^ 62 -> (forall i, a <= i < a + 1 -> PML.in_foot11 i /\ ~ (0xd5030 <= i < 0xd5032)) -> PML.u8 M' a v).
  { intros a v H Ha Hc. apply u8_x; [exact Ha | intros i Hi; destruct (Hc i Hi); apply KF; assumption | exact H]. }
  assert (X32 : forall a v, PML.u32 M a v -> 0 <= a < 2 ^ 62 -> (forall i, a <= i < a + 4 -> PML.in_foot11 i /\ ~ (0xd5030 <= i < 0xd5032)) -> PML.u32 M' a v).
  { intros a v H Ha Hc. apply u32_x; [exact Ha | intros i Hi; destruct (Hc i Hi); apply KF; assumption | exact H]. }
  assert (X64 : forall a v, PML.u64 M a v -> 0 <= a < 2 ^ 62 -> (forall i, a <= i < a + 8 -> PML.in_foot11 i /\ ~ (0xd5030 <= i < 0xd5032)) -> PML.u64 M' a v).
  { intros a v H Ha Hc. apply u64_x; [exact Ha | intros i Hi; destruct (Hc i Hi); apply KF; assumption | exact H]. }
  assert (LD : PML.loc_done M').
  { split; [apply (X8 _ _ G1); [lia | intros i Hi; split; [foot_cell | lia]]|]. split; [apply (X64 _ _ G2); [lia | intros i Hi; split; [foot_cell | lia]] | exact GD]. }
  assert (EG : forall b, PML.errcat_guard M b -> PML.errcat_guard M' b).
  { intros b (A & B). split; [apply (X8 _ _ A) | apply (X8 _ _ B)]; try lia; intros i Hi; (split; [foot_cell | lia]). }
  assert (CG : forall b, PML.convcat_guard M b -> PML.convcat_guard M' b).
  { intros b (A & B). split; [apply (X8 _ _ A) | apply (X8 _ _ B)]; try lia; intros i Hi; (split; [foot_cell | lia]). }
  assert (AC : forall hs, PML.atexit_cells M hs -> PML.atexit_cells M' hs).
  { intros hs (A & B & C & D & E & F & G & H). unfold PML.atexit_cells, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD in *.
    split; [apply (X8 _ _ A); [lia | intros i Hi; split; [foot_cell | lia]]|]. split; [apply (X32 _ _ B); [lia | intros i Hi; split; [foot_cell | lia]]|].
    split; [apply (X32 _ _ C); [lia | intros i Hi; split; [foot_cell | lia]]|]. split; [apply (X64 _ _ D); [lia | intros i Hi; split; [foot_cell | lia]]|].
    split; [apply (X64 _ _ E); [lia | intros i Hi; split; [foot_cell | lia]]|]. split; [apply (X64 _ _ F); [lia | intros i Hi; split; [foot_cell | lia]]|].
    split; [apply (X64 _ _ G); [lia | intros i Hi; split; [foot_cell | lia]]|].
    destruct hs as [|[f a] [|[f2 a2] [|h3 hs]]]; [exact I | | | exact H].
    - destruct H as (H1 & H2). split; [apply (X64 _ _ H1) | apply (X64 _ _ H2)]; try lia; intros i Hi; (split; [foot_cell | lia]).
    - destruct H as (H1 & H2 & H3 & H4).
      split; [apply (X64 _ _ H1); [lia | intros i Hi; split; [foot_cell | lia]]|]. split; [apply (X64 _ _ H2); [lia | intros i Hi; split; [foot_cell | lia]]|].
      split; [apply (X64 _ _ H3) | apply (X64 _ _ H4)]; try lia; intros i Hi; (split; [foot_cell | lia]). }
  destruct EC as (g & Hg & A & B & C).
  exists g. split; [exact Hg|]. split; [exact RO'|]. split; [exact LQ'|].
  destruct g; [exfalso; apply Hg; reflexivity | ..]; (split; [exact LD|]; split; [exact (EG _ A)|]; split; [exact (CG _ B) | exact (AC _ C)]).
Qed.
End Xfer.

Lemma u64_u8_low : forall (M : mem) a w, 0 <= a -> a + 8 <= 2 ^ 64 -> PML.u64 M a w -> PML.u8 M a (w mod 256).
Proof.
  intros M a w Ha Ha8 H. unfold PML.u64, PML.u8, L5.u64_at, L5.u8_at in *.
  assert (EQ : forall x n, rdn RSEGS M x (S n) = match (match M x with Some b => Some b | None => seg_rom RSEGS x end) with
                 | Some b => match rdn RSEGS M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  rewrite (EQ _ 7%nat) in H. rewrite (EQ _ 0%nat). cbn [rdn].
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn RSEGS M (Z_to_bv 64 a + 1)%bv 7) as [rest|] eqn:ER; [|discriminate].
  unfold word_to_le_bytes in H. cbn [Z_to_le_bytes] in H. injection H as H1 H2. f_equal. f_equal. rewrite H1. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. replace (2 ^ 64) with (256 * 2 ^ 56) by reflexivity. rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section Heap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.

Definition keepH (LBk : list (Z * Z)) (W : list L5.range) (sp scr : Z) (a : Z) : Prop :=
  L5.outside W a /\ (sp <= a \/ (hl_ceil L <= a < sp - scr) \/ in_block LBk a \/ (0x10000 <= a < 0xf8000 /\ ~ (0xf6c08 <= a < 0xf6fb0) /\ ~ (0xd675c <= a < 0xd6760))).
Definition blocks_ok (LB : list (Z * Z)) : Prop := forall b, In b LB -> block_range L (fst b) (snd b).
Lemma blocks_ok_heap : forall LB cr M VM, hi_heap HI LB cr M VM -> blocks_ok LB.
Proof. intros LB cr M VM HH b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). exact (proj1 (Hwf b Hb)). Qed.

Lemma hpres_samem : forall LBk sp scr W M M', L5C.hpres L LBk sp scr W M M' -> blocks_ok LBk -> L5C.stk (hl_sptop L) M sp scr -> 0 <= scr ->
  TK.samem (keepH LBk W sp scr) M M'.
Proof.
  intros LBk sp scr W M M' HP HB (S1 & S2 & S3 & S4 & S5) Hscr a Ha [HW HK]. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR.
  split; [exact Ha|]. unfold client_addr, in_errno. rewrite ILO, IHI, ERR. unfold hl_ceil in *.
  destruct HK as [HK|[HK|[HK|HK]]].
  - split; [right; left; lia|]. split; [lia | exact HW].
  - split; [right; left; lia|]. split; [lia | exact HW].
  - split; [left; exact HK|]. split; [|exact HW]. destruct HK as (b & Hb & Hr). destruct (HB b Hb) as (B0 & B1 & _). rewrite ILO, IHI in B1. lia.
  - split; [right; right; split; [lia|]; intros X; apply (PmLayout.ly_static L LAY) in X; lia|]. split; [lia | exact HW].
Qed.
Lemma frame_but_samem : forall F M M', L5.frame_but F M M' -> TK.samem (L5.outside F) M M'.
Proof. intros F M M' H a Ha Ho. apply H. rewrite L5.unsigned_lit by lia. exact Ho. Qed.

Lemma heap_stack_write : forall LB cr M M' VM lo hi, hi_heap HI LB cr M VM -> 0x7fff80000000 <= hl_sptop L -> hl_ceil L <= lo -> hi <= hl_sptop L ->
  TK.samem (fun a => ~ (lo <= a < hi)) M M' -> mem_grows M M' -> hi_heap HI LB cr M' VM.
Proof.
  intros LB cr M M' VM lo hi HH Htop Hlo Hhi AG MG. apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. apply AG; [exact Ha|]. intros Hin. destruct HP as [(P1 & _)|P]; [lia|].
    destruct (PmLayout.ly_ro L LAY a P) as [X|X]; [|lia]. rewrite (PmLayout.ly_img_hi L LAY) in X. unfold hl_ceil in Hlo. lia.
  - intros a Hd. apply MG. exact Hd.
Qed.

Lemma heap_pure_write : forall LB cr M M' VM (K : Z -> Prop), hi_heap HI LB cr M VM -> 0x7fff80000000 <= hl_sptop L -> TK.samem K M M' -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ K a -> (hl_ceil L <= a < hl_sptop L) \/ (0xbd000 <= a < 0xf6a70 /\ ~ (0xc3a48 <= a < 0xc3a50))) -> hi_heap HI LB cr M' VM.
Proof.
  intros LB cr M M' VM K HH Htop AG MG HK. apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. apply AG; [exact Ha|]. destruct (classic (K a)) as [Y|N]; [exact Y|]. exfalso.
    pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
    destruct (HK a Ha N) as [X|X].
    + destruct HP as [(P1 & _)|P]; [lia|]. destruct (PmLayout.ly_ro L LAY a P) as [Y|Y]; [rewrite IHI in Y; unfold hl_ceil in X; lia | lia].
    + destruct HP as [(P1 & P2 & P3)|P].
      * apply P3. rewrite ILO, IHI. split; [lia|]. intros Y. apply (PmLayout.ly_static L LAY) in Y. lia.
      * pose proof (PmLayout.ly_ro_img L LAY a P) as Y. rewrite ILO, IHI in Y. lia.
  - intros a Hd. apply MG. exact Hd.
Qed.

Definition FR (LB0 : list (Z * Z)) (sp0 SCR : Z) (foot : Z -> Prop) (M0 M : mem) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB0 sp0 SCR a -> ~ foot a -> ~ in_errno L a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) /\
  (forall a, sp0 - SCR <= a < sp0 -> M (Z_to_bv 64 a) <> None).
Lemma FR_samem : forall LB0 sp0 SCR foot M0 M M' (K : Z -> Prop), FR LB0 sp0 SCR foot M0 M -> TK.samem K M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB0 sp0 SCR a -> ~ foot a -> ~ in_errno L a -> K a) ->
  (forall a, sp0 - SCR <= a < sp0 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) -> FR LB0 sp0 SCR foot M0 M'.
Proof.
  intros LB0 sp0 SCR foot M0 M M' K [F1 F2] AG HK HD. split.
  - intros a Ha HC HF HE. rewrite (AG a Ha (HK a Ha HC HF HE)). apply F1; assumption.
  - intros a Ha. apply HD; [exact Ha | apply F2; exact Ha].
Qed.

Definition w_si (W : list L5.range) : Prop := forall w, In w W -> hl_ceil L <= fst w \/ (0x10000 <= fst w /\ fst w + snd w <= 0xf8000).
Lemma block_outside : forall W p cap i, w_si W -> block_range L p cap -> p <= i < p + cap -> L5.outside W i.
Proof.
  intros W p cap i HW (B0 & B1 & B2 & B3 & B4) Hi w Hw Hin. unfold L5.in_rng in Hin.
  rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1. destruct (HW w Hw) as [X|X]; lia.
Qed.
Lemma cov_block : forall LBk W sp scr p cap, w_si W -> In (p, cap) LBk -> block_range L p cap -> cov (keepH LBk W sp scr) p cap.
Proof.
  intros LBk W sp scr p cap HW Hin HB i Hi. split; [exact (block_outside W p cap i HW HB Hi)|]. right; right; left. exists (p, cap). split; [exact Hin | cbn [fst snd]; lia].
Qed.
Lemma str_cov_keepH : forall LBk W sp scr o r, hl_sptop L <= 2 ^ 47 -> cov (keepH LBk W sp scr) o 24 -> w_si W ->
  (forall b, In b (PML.srep_blocks r) -> In b LBk /\ block_range L (fst b) (snd b)) -> str_cov (keepH LBk W sp scr) o r.
Proof.
  intros LBk W sp scr o r Htop Ho HW HB. split; [exact Ho|]. destruct r as [s|cap p s]; [exact I|].
  destruct (HB (p, cap) (or_introl eq_refl)) as [Hin HR]. cbn [fst snd] in HR. pose proof HR as (B0 & B1 & B2 & B3 & B4).
  split; [lia|]. split; [lia|]. exact (cov_block LBk W sp scr p cap HW Hin HR).
Qed.
Lemma ps_cov_keepH : forall LBk W sp scr ps, hl_sptop L <= 2 ^ 47 -> w_si W -> (forall b, In b (PML.ps_blocks ps) -> In b LBk /\ block_range L (fst b) (snd b)) -> ps_cov (keepH LBk W sp scr) ps.
Proof.
  intros LBk W sp scr ps Htop HW HB. destruct (HB (PML.ps_bptr ps, PML.ps_bcap ps) (or_introl eq_refl)) as [I1 R1].
  destruct (HB (PML.ps_sb ps, PML.ps_scap ps) (or_intror (or_introl eq_refl))) as [I2 R2]. cbn [fst snd] in R1, R2.
  pose proof R1 as (B0 & B1 & B2 & B3 & B4). pose proof R2 as (C0 & C1 & C2 & C3 & C4).
  split; [lia|]. split; [lia|]. split; [exact (cov_block _ _ _ _ _ _ HW I1 R1)|]. split; [lia|]. split; [lia|]. exact (cov_block _ _ _ _ _ _ HW I2 R2).
Qed.
Lemma statics_cov_keepH : forall LBk W sp scr, (forall a, PML.in_foot11 a \/ (0x10000 <= a < PML.IMG_RO_HI \/ 0xf6a93 <= a < 0xf6a94 \/ 0xf6b68 <= a < 0xf6b6c) -> L5.outside W a) -> statics_cov (keepH LBk W sp scr).
Proof.
  intros LBk W sp scr HW. split; [|split].
  - intros a Ha. split; [apply HW; left; exact Ha|]. right; right; right. destruct Ha as (iv & Hiv & Hr). unfold PML.ll_foot_csrc in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
  - intros a Ha. split; [apply HW; right; left; exact Ha|]. right; right; right. unfold PML.IMG_RO_HI in Ha. lia.
  - intros a Ha. split; [apply HW; right; right; exact Ha|]. right; right; right. lia.
Qed.

Lemma statics_cov_lo : forall K : Z -> Prop, (forall a, 0x10000 <= a < 0xf8000 -> K a) -> statics_cov K.
Proof.
  intros K H. split; [|split].
  - intros a (iv & Hiv & Hr). apply H. unfold PML.ll_foot_csrc in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn in Hr; lia|]). destruct Hiv.
  - intros a Ha. apply H. unfold PML.IMG_RO_HI in Ha. lia.
  - intros a Ha. apply H. lia.
Qed.

Lemma cov_block_out : forall F p cap, w_si F -> block_range L p cap -> cov (L5.outside F) p cap.
Proof. intros F p cap HW HB i Hi. exact (block_outside F p cap i HW HB Hi). Qed.
Lemma str_cov_out : forall F o r, hl_sptop L <= 2 ^ 47 -> cov (L5.outside F) o 24 -> w_si F -> (forall b, In b (PML.srep_blocks r) -> block_range L (fst b) (snd b)) -> str_cov (L5.outside F) o r.
Proof.
  intros F o r Htop Ho HW HB. split; [exact Ho|]. destruct r as [s|cap p s]; [exact I|].
  pose proof (HB (p, cap) (or_introl eq_refl)) as HR. cbn [fst snd] in HR. pose proof HR as (B0 & B1 & B2 & B3 & B4).
  split; [lia|]. split; [lia|]. exact (cov_block_out F p cap HW HR).
Qed.
Lemma ps_cov_out : forall F ps, hl_sptop L <= 2 ^ 47 -> w_si F -> (forall b, In b (PML.ps_blocks ps) -> block_range L (fst b) (snd b)) -> ps_cov (L5.outside F) ps.
Proof.
  intros F ps Htop HW HB. pose proof (HB (PML.ps_bptr ps, PML.ps_bcap ps) (or_introl eq_refl)) as R1.
  pose proof (HB (PML.ps_sb ps, PML.ps_scap ps) (or_intror (or_introl eq_refl))) as R2. cbn [fst snd] in R1, R2.
  pose proof R1 as (B0 & B1 & B2 & B3 & B4). pose proof R2 as (C0 & C1 & C2 & C3 & C4).
  split; [lia|]. split; [lia|]. split; [exact (cov_block_out _ _ _ HW R1)|]. split; [lia|]. split; [lia|]. exact (cov_block_out _ _ _ HW R2).
Qed.
Lemma statics_cov_out : forall F, (forall w, In w F -> hl_ceil L <= fst w) -> 0x7fff80000000 <= hl_sptop L -> statics_cov (L5.outside F).
Proof.
  intros F HF Htop. assert (X : forall a, a < 0xf8000 -> L5.outside F a) by (intros a Ha w Hw Hin; unfold L5.in_rng in Hin; specialize (HF w Hw); lia).
  split; [|split]; intros a Ha; apply X; [destruct Ha as (iv & Hiv & Hr); unfold PML.ll_foot_csrc in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]); destruct Hiv | unfold PML.IMG_RO_HI in Ha; lia | lia].
Qed.

Lemma samem_out1 : forall (M M' : mem) lo n, TK.samem (fun a => ~ (lo <= a < lo + n)) M M' -> TK.samem (L5.outside [(lo, n)]) M M'.
Proof. intros M M' lo n H. apply (TK.samem_weaken _ _ _ _ H). intros a Ho Hin. apply (Ho (lo, n) (or_introl eq_refl)). exact Hin. Qed.

Lemma client_not_window : forall LB0 sp0 SCR a, client_addr L LB0 sp0 SCR a -> blocks_ok LB0 -> hl_ceil L + SCR <= sp0 -> 0x7fff80000000 <= hl_sptop L -> ~ (sp0 - SCR <= a < sp0).
Proof.
  intros LB0 sp0 SCR a HC HB Hc Htop Hin. pose proof (PmLayout.ly_img_hi L LAY) as IHI. unfold hl_ceil in *.
  destruct HC as [(b & Hb & Hr)|[(C1 & C2)|(C1 & _)]]; [destruct (HB b Hb) as (_ & _ & _ & _ & B4); unfold hl_ceil in B4; lia | lia | rewrite IHI in C1; lia].
Qed.
Lemma FR_hpres : forall LB0 sp0 SCR foot M0 M M' LBk spc scr W,
  FR LB0 sp0 SCR foot M0 M -> L5C.hpres L LBk spc scr W M M' -> blocks_ok LB0 -> incl LB0 LBk ->
  hl_ceil L + SCR <= sp0 -> 0x7fff80000000 <= hl_sptop L -> sp0 <= 2 ^ 47 -> sp0 - SCR <= spc - scr -> spc <= sp0 -> 0 <= scr ->
  (forall w a, In w W -> L5.in_rng w a -> (sp0 - SCR <= a < sp0) \/ foot a) -> FR LB0 sp0 SCR foot M0 M'.
Proof.
  intros LB0 sp0 SCR foot M0 M M' LBk spc scr W [F1 F2] HP HB Hincl Hc Htop Hsp47 Hlo Hhi Hscr HW.
  pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR. split.
  - intros a Ha HC HF HE. rewrite <- (F1 a Ha HC HF HE). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
    pose proof (client_not_window _ _ _ _ HC HB Hc Htop) as NW.
    split; [exact Ha|]. split; [|split; [exact HE|]].
    + destruct HC as [(b & Hb & Hr)|[(C1 & C2)|C]]; [left; exists b; split; [apply Hincl; exact Hb | exact Hr] | right; left; split; [exact C1 | lia] | right; right; exact C].
    + intros w Hw Hin. destruct (HW w a Hw Hin) as [X|X]; [exact (NW X) | exact (HF X)].
  - intros a Ha. destruct (Z_le_dec (spc - scr) a) as [G1|G1]; [destruct (Z_lt_dec a spc) as [G2|G2]|].
    + pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP (a - (spc - scr)) ltac:(lia)) as Y. replace (spc - scr + (a - (spc - scr))) with a in Y by lia. exact Y.
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP); [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite ERR; unfold hl_ceil in *; lia | exact (F2 a Ha)].
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP); [unfold hl_ceil in *; lia | right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite ERR; unfold hl_ceil in *; lia | exact (F2 a Ha)].
Qed.

Lemma FR_grows : forall LB0 sp0 SCR foot M0 M M' (K : Z -> Prop), FR LB0 sp0 SCR foot M0 M -> TK.samem K M M' -> mem_grows M M' -> blocks_ok LB0 ->
  hl_ceil L + SCR <= sp0 -> 0x7fff80000000 <= hl_sptop L -> (forall a, ~ K a -> (sp0 - SCR <= a < sp0) \/ foot a) -> FR LB0 sp0 SCR foot M0 M'.
Proof.
  intros LB0 sp0 SCR foot M0 M M' K HF AG MG HB Hc Htop HK. apply (FR_samem _ _ _ _ _ _ _ K HF AG).
  - intros a Ha HC Hf He. destruct (classic (K a)) as [Y|N]; [exact Y|]. exfalso. destruct (HK a N) as [X|X]; [exact (client_not_window _ _ _ _ HC HB Hc Htop X) | exact (Hf X)].
  - intros a Ha Hd. apply MG. exact Hd.
Qed.
End Heap.
End TK2.
