(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RB.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Definition wp (ps : PML.pstate) : Z := match PML.ps_win ps with Some (p, _) => p | None => 0 end.
Definition we (ps : PML.pstate) : Z := match PML.ps_win ps with Some (_, e) => e | None => 0 end.
Lemma win_cells : forall M P ps, PML.parser_at M P ps -> PML.u64 M (P + 200) (wp ps) /\ PML.u64 M (P + 192) (we ps) /\ wp ps <= we ps.
Proof.
  intros M P ps H. unfold PML.parser_at in H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Aw & _).
  unfold wp, we. destruct (PML.ps_win ps) as [[p e]|]; [destruct Aw as (A & B & C); auto | destruct Aw as (A & B); split; [exact B | split; [exact A | lia]]].
Qed.
Lemma exhausted_iff : forall ps, PMS.win_exhausted ps <-> wp ps = we ps.
Proof. intros ps. unfold PMS.win_exhausted, wp, we. destruct (PML.ps_win ps) as [[p e]|]; [reflexivity | split; auto]. Qed.
Lemma set_win_same : forall ps, PML.ps_set_win ps (PML.ps_win ps) = ps.
Proof. intros []. reflexivity. Qed.

Lemma reader_split : forall M R IS V ch bof ps, PML.reader_at M R IS V ch bof ps ->
  TPS.rdr_at M R IS V ch bof /\ PML.parser_at M (R + 320) ps /\ match PML.ps_win ps with None => True | Some (p, e) => ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) end.
Proof.
  intros M R IS V ch bof ps (A240 & A248 & A264 & A272 & Ade & A288 & A296 & A304 & A312 & Aio & A32 & Apar & Awin & Adef).
  split; [|split; [exact Apar | exact Awin]]. unfold TPS.rdr_at. repeat (split; [assumption|]). apply (L5.defined_sub _ _ _ _ _ Adef); lia.
Qed.
Lemma rdr_source : forall M R IS V ch bof, TPS.rdr_at M R IS V ch bof -> PML.source_at M R ch.
Proof. intros M R IS V ch bof (A240 & A248 & A264 & A272 & Ade & A288 & A296 & A304 & A312 & Aio & A32 & Adef). split; [exact A264 | split; [exact A272 | split; [exact Aio | split; [exact A32 | exact Adef]]]]. Qed.

Section Xfer.
Variable K : Z -> Prop.
Variables M M' : mem.
Hypothesis AG : TK.samem K M M'.
Lemma rdr_at_x : forall R IS V ch bof, 0 <= R < 2 ^ 59 -> TK2.cov K R 320 -> TPS.rdr_at M R IS V ch bof -> TPS.rdr_at M' R IS V ch bof.
Proof.
  intros R IS V ch bof HR HK H. unfold TPS.rdr_at in *.
  destruct H as (A240 & A248 & A264 & A272 & (de & A280 & Hde) & A288 & A296 & A304 & A312 & (st0 & Aio) & A32 & Adef).
  repeat (split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption]|]).
  split; [exists de; split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption] | exact Hde]|].
  split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption]|].
  split; [apply (TK2.u8_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | assumption]|].
  repeat (split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption]|]).
  split; [exists st0; apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact Aio]|].
  split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption]|].
  apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Adef].
Qed.

Lemma win_ok_x : forall LBo ps, (forall b, In b LBo -> 0 <= fst b /\ fst b + snd b <= 2 ^ 62 /\ TK2.cov K (fst b) (snd b)) -> PML.win_ok M LBo ps -> PML.win_ok M' LBo ps.
Proof.
  intros LBo ps HB H. unfold PML.win_ok in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I].
  destruct H as (ch & Hin & H1 & H2 & Hd). exists ch. split; [exact Hin|]. split; [exact H1|]. split; [exact H2|].
  destruct (HB _ Hin) as (B0 & B1 & B2). cbn [fst snd] in *.
  destruct (Z_le_gt_dec e p) as [G|G]; [intros i Hi; lia|].
  apply (TK.defined_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply B2; lia | exact Hd].
Qed.
End Xfer.

Lemma parser_at_setwin : forall (M M' : mem) P ps w',
  PML.parser_at M P ps -> TK.samem (fun a => ~ (P + 192 <= a < P + 208)) M M' -> mem_grows M M' -> 0 <= P < 2 ^ 60 ->
  (0 <= PML.ps_bptr ps /\ PML.ps_bptr ps + PML.ps_bcap ps < 2 ^ 62 /\ (PML.ps_bptr ps + PML.ps_bcap ps <= P \/ P + 272 <= PML.ps_bptr ps)) ->
  (0 <= PML.ps_sb ps /\ PML.ps_sb ps + PML.ps_scap ps < 2 ^ 62 /\ (PML.ps_sb ps + PML.ps_scap ps <= P \/ P + 272 <= PML.ps_sb ps)) ->
  match w' with None => PML.u64 M' (P + 192) 0 /\ PML.u64 M' (P + 200) 0 | Some (p, e) => PML.u64 M' (P + 200) p /\ PML.u64 M' (P + 192) e /\ p <= e end ->
  PML.parser_at M' P (PML.ps_set_win ps w').
Proof.
  intros M M' P ps w' H AG MG HP (B1 & B2 & B3) (S1 & S2 & S3) HW. unfold PML.parser_at in *.
  destruct H as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  set (K := fun a => ~ (P + 192 <= a < P + 208)) in *.
  assert (C : forall a n, a + n <= P + 192 \/ P + 208 <= a -> TK2.cov K a n) by (intros a n Ha i Hi; unfold K; lia).
  destruct ps as [st sst nst more done level stack sb scap bcap bptr buf win]. cbn [PML.ps_set_win PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in *.
  repeat (split; [first [apply (TK2.u64_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u32_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u8_x K M M' AG); [lia | apply C; lia | assumption]
                        | apply (TK2.lstr_short_x K M M' AG); [lia | apply C; lia | assumption] ]|]).
  split; [exact HW|].
  repeat (split; [first [apply (TK2.u64_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u32_x K M M' AG); [lia | apply C; lia | assumption] | apply (TK2.u8_x K M M' AG); [lia | apply C; lia | assumption]]|]).
  split; [apply (TK2.str_at_x K M M' AG); [lia | split; [apply C; lia | split; [lia | split; [lia | apply C; lia]]] | exact Abuf]|].
  split; [exact Abc|].
  repeat (split; [apply (TK2.u64_x K M M' AG); [lia | apply C; lia | assumption]|]).
  split; [apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; unfold K; lia | exact Astk]|].
  split; [exact Asl|]. exact (L5.defined_grows M M' _ _ MG Adef).
Qed.

Lemma parser_at_patch : forall (K : Z -> Prop) (M M' : mem) P ps,
  PML.parser_at M P ps -> TK.samem K M M' -> L5.defined M' P 272 -> 0 <= P < 2 ^ 60 ->
  (0 <= PML.ps_bptr ps /\ PML.ps_bptr ps + PML.ps_bcap ps < 2 ^ 62 /\ TK2.cov K (PML.ps_bptr ps) (PML.ps_bcap ps)) ->
  TK2.cov K P 144 -> TK2.cov K (P + 192) 16 -> TK2.cov K (P + 209) 2 -> TK2.cov K (P + 213) 35 ->
  (TK2.cov K (P + 144) 4 \/ PML.u32 M' (P + 144) (PML.ps_level ps)) -> (TK2.cov K (P + 208) 1 \/ PML.u8 M' (P + 208) (PML.ps_st ps)) ->
  (TK2.cov K (P + 211) 1 \/ PML.u8 M' (P + 211) (PML.b2z (PML.ps_more ps))) -> (TK2.cov K (P + 212) 1 \/ PML.u8 M' (P + 212) (PML.b2z (PML.ps_done ps))) ->
  ((TK2.cov K (P + 248) 24 /\ 0 <= PML.ps_sb ps /\ PML.ps_sb ps + PML.ps_scap ps < 2 ^ 62 /\ TK2.cov K (PML.ps_sb ps) (PML.ps_scap ps)) \/
   (PML.u64 M' (P + 248) (PML.ps_sb ps) /\ PML.u64 M' (P + 256) (PML.ps_sb ps + Z.of_nat (length (PML.ps_stack ps))) /\ PML.u64 M' (P + 264) (PML.ps_sb ps + PML.ps_scap ps) /\
    L5.bytes_at RSEGS M' (PML.ps_sb ps) (PML.ps_stack ps))) ->
  PML.parser_at M' P ps.
Proof.
  intros K M M' P ps H AG DEF HP (B1 & B2 & B3) C0 CW C209 C213 PL PS PM PD PK. unfold PML.parser_at in *.
  destruct H as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  assert (X64 : forall C lo len a v, TK2.cov K lo len -> C = (lo, len) -> lo <= a -> a + 8 <= lo + len -> 0 <= a < 2 ^ 62 -> PML.u64 M a v -> PML.u64 M' a v).
  { intros C lo len a v HC _ H1 H2 H3 H4. apply (TK2.u64_x K M M' AG); [exact H3 | eapply TK2.cov_sub; [exact HC | lia | lia] | exact H4]. }
  assert (X32 : forall lo len a v, TK2.cov K lo len -> lo <= a -> a + 4 <= lo + len -> 0 <= a < 2 ^ 62 -> PML.u32 M a v -> PML.u32 M' a v).
  { intros lo len a v HC H1 H2 H3 H4. apply (TK2.u32_x K M M' AG); [exact H3 | eapply TK2.cov_sub; [exact HC | lia | lia] | exact H4]. }
  assert (X8 : forall lo len a v, TK2.cov K lo len -> lo <= a -> a + 1 <= lo + len -> 0 <= a < 2 ^ 62 -> PML.u8 M a v -> PML.u8 M' a v).
  { intros lo len a v HC H1 H2 H3 H4. apply (TK2.u8_x K M M' AG); [exact H3 | eapply TK2.cov_sub; [exact HC | lia | lia] | exact H4]. }
  assert (XS : forall a s, P <= a -> a + 24 <= P + 144 -> L5.lstr_short RSEGS M a s -> L5.lstr_short RSEGS M' a s).
  { intros a s H1 H2 H3. apply (TK2.lstr_short_x K M M' AG); [lia | eapply TK2.cov_sub; [exact C0 | lia | lia] | exact H3]. }
  split; [apply (X64 (P, 144) P 144 _ _ C0 eq_refl); [lia | lia | lia | exact A0]|].
  split; [apply (X32 P 144 _ _ C0); [lia | lia | lia | exact A8]|].
  split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A12]|]. split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A13]|].
  split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A14]|]. split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A15]|].
  split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A16]|]. split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A17]|].
  split; [apply (X8 P 144 _ _ C0); [lia | lia | lia | exact A18]|].
  split; [apply XS; [lia | lia | exact A24]|]. split; [apply XS; [lia | lia | exact A48]|]. split; [apply XS; [lia | lia | exact A72]|].
  split; [apply (X64 (P, 144) P 144 _ _ C0 eq_refl); [lia | lia | lia | exact A96]|].
  split; [apply (X64 (P, 144) P 144 _ _ C0 eq_refl); [lia | lia | lia | exact A128]|].
  split; [destruct PL as [C|X]; [apply (X32 (P + 144) 4 _ _ C); [lia | lia | lia | exact A144] | exact X]|].
  split.
  { destruct (PML.ps_win ps) as [[p e]|]; [destruct Aw as (W1 & W2 & W3) | destruct Aw as (W1 & W2)]; repeat split; try assumption;
      (apply (X64 (P + 192, 16) (P + 192) 16 _ _ CW eq_refl); [lia | lia | lia | assumption]). }
  split; [destruct PS as [C|X]; [apply (X8 (P + 208) 1 _ _ C); [lia | lia | lia | exact A208] | exact X]|].
  split; [apply (X8 (P + 209) 2 _ _ C209); [lia | lia | lia | exact A209]|]. split; [apply (X8 (P + 209) 2 _ _ C209); [lia | lia | lia | exact A210]|].
  split; [destruct PM as [C|X]; [apply (X8 (P + 211) 1 _ _ C); [lia | lia | lia | exact A211] | exact X]|].
  split; [destruct PD as [C|X]; [apply (X8 (P + 212) 1 _ _ C); [lia | lia | lia | exact A212] | exact X]|].
  split; [apply (X8 (P + 213) 35 _ _ C213); [lia | lia | lia | exact A213]|].
  split; [apply (X32 (P + 213) 35 _ _ C213); [lia | lia | lia | exact A216]|].
  split; [apply (TK2.str_at_x K M M' AG); [lia | split; [eapply TK2.cov_sub; [exact C213 | lia | lia] | split; [exact B1 | split; [exact B2 | exact B3]]] | exact Abuf]|].
  split; [exact Abc|].
  destruct PK as [(CK & S1 & S2 & S3)|(K1 & K2 & K3 & K4)].
  - split; [apply (X64 (P + 248, 24) (P + 248) 24 _ _ CK eq_refl); [lia | lia | lia | exact A248]|].
    split; [apply (X64 (P + 248, 24) (P + 248) 24 _ _ CK eq_refl); [lia | lia | lia | exact A256]|].
    split; [apply (X64 (P + 248, 24) (P + 248) 24 _ _ CK eq_refl); [lia | lia | lia | exact A264]|].
    split; [apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply S3; lia | exact Astk]|].
    split; [exact Asl | exact DEF].
  - split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact Asl | exact DEF].
Qed.

Lemma u8_mod : forall (M : mem) a v, PML.u8 M a v -> PML.u8 M a (v mod 256).
Proof.
  intros M a v H. unfold PML.u8, L5.u8_at in *. rewrite H. do 2 f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma u32_u8_low : forall (M : mem) a w, 0 <= a -> a + 4 <= 2 ^ 64 -> 0 <= w < 256 -> PML.u32 M a w -> PML.u8 M a w.
Proof.
  intros M a w Ha Ha4 Hw H. unfold PML.u32, PML.u8, L5.u32_at, L5.u8_at in *.
  assert (EQ : forall x n, rdn RSEGS M x (S n) = match (match M x with Some b => Some b | None => seg_rom RSEGS x end) with
                 | Some b => match rdn RSEGS M (x + 1)%bv n with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  rewrite (EQ _ 3%nat) in H. rewrite (EQ _ 0%nat). cbn [rdn].
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn RSEGS M (Z_to_bv 64 a + 1)%bv 3) as [rest|] eqn:ER; [|discriminate].
  unfold word_to_le_bytes in H. cbn [Z_to_le_bytes] in H. injection H as H1 H2. f_equal. f_equal. rewrite H1. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small w (2 ^ 64)) by lia. reflexivity.
Qed.

Section Heap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.

Lemma heap_write_blk : forall LB cr M M' VM (K : Z -> Prop), hi_heap HI LB cr M VM -> 0x7fff80000000 <= hl_sptop L -> TK.samem K M M' -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ K a -> (hl_ceil L <= a < hl_sptop L) \/ (0xbd000 <= a < 0xf6a70 /\ ~ (0xc3a48 <= a < 0xc3a50)) \/ in_block LB a) -> hi_heap HI LB cr M' VM.
Proof.
  intros LB cr M M' VM K HH Htop AG MG HK. apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. apply AG; [exact Ha|]. destruct (classic (K a)) as [Y|N]; [exact Y|]. exfalso.
    pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
    destruct (HK a Ha N) as [X|[X|X]].
    + destruct HP as [(P1 & _)|P]; [lia|]. destruct (PmLayout.ly_ro L LAY a P) as [Y|Y]; [rewrite IHI in Y; unfold hl_ceil in X; lia | lia].
    + destruct HP as [(P1 & P2 & P3)|P].
      * apply P3. rewrite ILO, IHI. split; [lia|]. intros Y. apply (PmLayout.ly_static L LAY) in Y. lia.
      * pose proof (PmLayout.ly_ro_img L LAY a P) as Y. rewrite ILO, IHI in Y. lia.
    + destruct HP as [(P1 & P2 & P3)|P]; [exact (P2 X)|].
      destruct X as (b & Hb & Hr). destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & _). destruct (Hwf b Hb) as ((B0 & B1 & B2 & B3 & B4) & _).
      destruct (PmLayout.ly_ro L LAY a P) as [Y|Y]; [rewrite ILO, IHI in *; lia | unfold hl_ceil in B4; lia].
  - intros a Hd. apply MG. exact Hd.
Qed.
End Heap.
End RB.
