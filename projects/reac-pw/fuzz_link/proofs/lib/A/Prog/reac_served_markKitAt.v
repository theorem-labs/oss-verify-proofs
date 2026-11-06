(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the entry Pre's facts restated at a cut of the walk, for a
   callee of window Kc (0 <= Kc <= REAC_CODE_EMIT_AK) called on the realigned sp:
   the name (srm_name_at), a live interface-table string (srm_table_at), the policy literals
   (srm_policy_at), errno (srm_errno_at), g_nl's shadow (srm_gnl_sh_at), the marks block (srm_marks_blk_at) and the
   FILE block (srm_file_blk_at), over the memory at the cut `rdW W3 (ms_mem ms3)` and the callee's registers.
   Each byte the Pre reads through a pointer is an `akb` byte of the entry (the read set, Defs' srm_gspan_ok); its
   value comes from reac_served_markKit.v srm_view_kept and its shadow from lib/A/Prog/LinkWalkShadow.v
   shadow_transport_akb. The 8 bytes past the marks block are visible at every AR
   state (srm_blk_tail_vis16: the rest of the block's chunk is AR's junk, libreac/fuzz_boxreg BoxTailVis.v
   ar_blk_tail_vis on origin/ossv/recipes, here to the next multiple of 16). The rest of a string's NUL granule is
   not in the read set (the contract's W6 revert, ab90b9e2923d): srm_tail_vis carries its visibility from the entry
   to the cut by the four cases of `akb` of the NUL (the stack row: akept keeps presence there; a heap block: AR's
   block law and the chunk's junk; the image: the ROM fallback, lib/A/AB13.v tfib_rom_all; a side frame of the
   entry: AR's frame law at the cut).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB13.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markDefs reac_served_markUniq reac_served_markKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the bytes past a heap block, to the next multiple of 16 of its size, are visible at every AR state ---- *)
Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma srm_chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma srm_chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
  (ck_extent k - ck_rz k) mod 16 = 0.
Proof.
  intros ly S rd k M Hk.
  pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & RZ & _ & _ & G).
  assert (EX : ck_extent k mod 16 = 0).
  { destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct G].
    - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & _).
      pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _). rewrite Gext.
      apply Z.mod_divide in K2 as [q K2]; [|lia]. rewrite K2. replace (q * 32) with ((q * 2) * 16) by lia.
      apply Z.mod_mul. lia.
    - destruct G as (_ & Hp & _ & Gext & _). pose proof (secondary_geometry (ck_req k)) as SG.
      pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & Hn & _).
      destruct (SG ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _). rewrite Gext.
      apply Z.mod_divide in S5 as [q S5]; [|unfold kPage; lia]. rewrite S5. unfold kPage.
      replace (q * 4096 - 4096) with ((q * 256 - 256) * 16) by lia. apply Z.mod_mul. lia. }
  apply Z.mod_divide in EX as [a EX]; [|lia]. apply Z.mod_divide in RZ as [b RZ]; [|lia].
  rewrite EX, RZ. replace (a * 16 - b * 16) with ((a - b) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma srm_blk_tail_vis16 : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + n <= a < p + round_up n 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. subst u r.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (srm_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (N1 : 1 <= n).
  { destruct (Z.eq_dec n 0) as [->|]; [|lia]. unfold round_up in Ha. cbn in Ha. lia. }
  assert (CN : ck_n k = n) by (unfold ck_n, req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
  assert (RU : round_up n 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. unfold ck_n in CN. lia. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (srm_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + n) + (a - (ck_base B ly k + (ck_rz k + n)))) by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.

(* the same past a block of any request (req_size 0 = 1): the bytes after its req_size bytes *)
Lemma srm_blk_tail_vis16r : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= a < p + round_up (req_size n) 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er.
  assert (Hrn : ck_req k = n) by congruence.
  subst u.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (srm_chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (CN : ck_n k = req_size n) by (unfold ck_n; rewrite <- Hrn; reflexivity).
  assert (RU : round_up (req_size n) 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. first [lia | rewrite <- CN; lia | unfold ck_n in *; lia]. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (srm_chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + (ck_rz k + req_size n))))
    by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

Section k. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.

Ltac srm_unpreA H :=
  unfold srm_pre in H; destruct H as (HA & Prd & HP);
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14);
  destruct HP as (pkbs & ptab & pnm & pk & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14
                  & P15 & P16).

Ltac srm_unbaseA H :=
  unfold srm_base in H; cbv zeta in H;
  destruct H as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18
                 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).

Lemma srm_pa_img : forall a, in_img SEGS a -> 0x10000 <= a < pcap_img_end.
Proof. exact pa_img_range. Qed.

(* the shadow facts of an entry read-set range, at the cut *)
Lemma srm_shtr : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 p n,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 < n -> (forall a, p <= a < p + n ->
    akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a) ->
  range_addressable (ard SEGS (srm_m0 cx)) SHADOW_OFF p n -> shadow_hull_vis (ard SEGS (srm_m0 cx)) p n ->
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF p n /\
  shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms3))) p n.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 p n Hpre Hb HX Hn Hakb Hra Hhv.
  destruct (srm_lyeq SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (Hfa & Hfl & Hlo & Hhi & HAR3).
  pose proof (srm_kept_noside SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hb) as HK.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'. pose proof Hb as Hb'. srm_unbaseA Hb'.
  pose proof A1 as (_ & _ & (memS & HJ & _) & _). destruct HJ as (HARc & _).
  assert (Hbl : forall b m, In (b, m) (ablocks B (sm_lyc cx) (sm_Sc cx)) -> In (b, m) (ablocks B ly3 S3)).
  { intros b m Hbm. eapply Permutation_in; [apply Permutation_sym; exact B10 | exact Hbm]. }
  assert (Happ : forall a, X a -> a < kLowMemEnd \/ kHighMemBeg <= a).
  { intros a Ha. exact (proj2 (srm_E_app SK B LAWS TB RELRO_IMG HSEGS cx a Hpre (HX a Ha))). }
  assert (Himg := srm_pa_img).
  assert (Hfm : fmiss (sm_lyc cx) (sm_Sc cx) X) by (eapply fmiss_app; eassumption).
  change (ard SEGS (rdW W3 (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
  change (ard SEGS (srm_m0 cx)) with (aview SEGS (w_H (sm_W cx)) (sm_memc cx)) in Hra, Hhv.
  eapply shadow_transport_akb with (lyc := sm_lyc cx) (Sc := sm_Sc cx) (W := sm_W cx) (memc := sm_memc cx)
    (mdc := sm_mdc cx) (ly2 := ly3) (S2 := S3) (md2 := md3) (E := X); [eassumption ..].
Qed.

(* every byte of [lo, hi) has a byte in the image's file (seg_rom), so it is visible in every memory *)
Definition srm_rom_b (lo hi : Z) : bool :=
  forallb (fun i => match seg_rom tfibsegs (Z_to_bv 64 (lo + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (hi - lo))).

Lemma srm_rom_vis : forall lo hi a (H : word -> bool) (m : word -> option byte),
  srm_rom_b lo hi = true -> lo <= a < hi -> aview SEGS H m a <> None.
Proof using HSEGS.
  intros lo hi a H m Hb Ha. rewrite HSEGS. unfold srm_rom_b in Hb. rewrite forallb_forall in Hb.
  assert (Hin : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat (hi - lo)))) by (apply in_seq; lia).
  specialize (Hb (Z.to_nat (a - lo)) Hin). cbv beta in Hb.
  rewrite Z2Nat.id in Hb by lia. replace (lo + (a - lo)) with a in Hb by lia.
  unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)); cbn [option_map]; [discriminate | discriminate Hb].
Qed.

(* a byte of the image's file range [0x10000, pcap_img_end) is visible in every memory: mbyte falls back to seg_rom
   (YP09.v:18-22), which is Some on all of it (AB13.v:148 tfib_rom_all) *)
Lemma srm_img_vis : forall a (H : word -> bool) (m : word -> option byte),
  0x10000 <= a < pcap_img_end -> aview SEGS H m a <> None.
Proof using HSEGS.
  intros a H m Ha. rewrite HSEGS. unfold aview, mbyte.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [x|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)) eqn:Er; cbn [option_map]; [discriminate|].
  exfalso. exact (AB13.tfib_rom_all a Ha Er).
Qed.

(* a present byte is visible; a visible byte off the image is present (seg_rom has nothing there) *)
Lemma srm_present_vis : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview SEGS H m a <> None.
Proof.
  intros H m a [Hh [x Hx]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hx. discriminate.
Qed.

Lemma srm_vis_present : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H m a <> None -> apresent H m a.
Proof.
  intros H m a Ha Hn Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
  rewrite (seg_rom_none SEGS a Ha Hn) in Hv.
  destruct (H (Z_to_bv 64 a)); [exfalso; exact (Hv eq_refl)|]. split; [reflexivity|].
  destruct (m (Z_to_bv 64 a)) as [x|]; [exists x; reflexivity | exfalso; exact (Hv eq_refl)].
Qed.

(* THE REST OF A NUL'S GRANULE at a cut. e is a byte the call keeps (`akb` at the entry: the NUL of the name or of a
   live table string, the read set's last byte); b lies past it in its 8-byte granule and is visible at the entry
   (astr_rt_ok's tail clause of the Pre). Then b is visible at the cut, by the four cases of e:
   - the real-stack row outside [sp - K, sp) (both ends 16-aligned, so b is outside the window too): b is above
     alloc_ceiling and off the image, so its visibility at the entry is presence, and akept's presence clause
     (srm_base's akept, clause 5) keeps it;
   - a heap block (q, m) of Sc: b < q + round_up (req_size m) 16 (q is 16-aligned); the block is the cut's
     (srm_base's Permutation), whose bytes AR's block law makes present and whose tail srm_blk_tail_vis16r makes
     visible;
   - an image byte: b < pcap_img_end (page-aligned), so the ROM fallback (srm_img_vis);
   - a side frame (c, q) of Sc: frames are 32-aligned and of 64 << c bytes, so b is in the frame, which is in
     frames S3, and AR's frame law at the cut makes it present. *)
Lemma srm_tail_vis : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 e b,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) e ->
  e < b < e - e mod 8 + 8 ->
  aview SEGS (w_H (sm_W cx)) (sm_memc cx) b <> None ->
  aview SEGS (w_H W3) (ms_mem ms3) b <> None.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 e b Hpre Hb He Heb Hv0.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm8.
  destruct (srm_lyeq SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (Hfa & _ & _ & _ & HAR3).
  pose proof Hb as Hb'. srm_unbaseA Hb'.
  destruct He as [(Hs1 & Hs2) | [(q & m & Hqm & Hq) | [(Hi & _ & _) | (c & q & Hcq & Hr)]]].
  - (* the real-stack row *)
    pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & _ & _).
    pose proof Hpre as Hpre'. srm_unpreA Hpre'.
    pose proof A1 as HR. eapply ajournal_gx_row in HR. destruct HR as (R1 & R2 & _ & _).
    pose proof REAC_SERVED_MARK_AK_val as HK.
    pose proof asan_consts as ((C1a & C1b) & _).
    pose proof srm_pow as (P47 & P64).
    assert (Hnw : ~ (srm_sp cx - REAC_SERVED_MARK_AK <= b < srm_sp cx)) by lia.
    assert (Hni : ~ in_img SEGS b).
    { intros Hib. pose proof (srm_pa_img b Hib) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia. }
    destruct B29 as (_ & _ & _ & _ & K5 & _).
    apply srm_present_vis. apply K5; [lia | exact Hnw |].
    apply srm_vis_present; [lia | exact Hni | exact Hv0].
  - (* a heap block of the entry *)
    assert (Hq3 : In (q, m) (ablocks B ly3 S3)).
    { eapply Permutation_in; [apply Permutation_sym; exact B10 | exact Hqm]. }
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hq3) as (Hal & _ & _ & _ & Hpr & _).
    destruct (Z_lt_le_dec b (q + req_size m)) as [Hin | Hout].
    + apply srm_present_vis. exact (proj1 (Hpr b ltac:(lia))).
    + apply (srm_blk_tail_vis16r SEGS B ly3 S3 W3 (ms_mem ms3) md3 q m b HAR3 Hq3).
      split; [exact Hout|]. unfold round_up. lia.
  - (* an image byte *)
    pose proof (srm_pa_img e Hi) as (He1 & He2).
    apply srm_img_vis. unfold pcap_img_end, YImgTop.IMG_TOP in *. lia.
  - (* a side frame of the entry *)
    assert (Hc3 : In (c, q) (frames S3)) by (rewrite B7; right; exact Hcq).
    destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hc3) as (Hal & _ & Hpr & _).
    pose proof HAR3 as [M3 _].
    destruct (frame_facts B ly3 S3 _ c q M3 Hc3) as ((Hc0 & Hc10) & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite <- (Hfa c q) in Hr.
    assert (F8 : fs_frame_bytes c mod 8 = 0).
    { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
      replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by ring. apply Z.mod_mul. lia. }
    apply srm_present_vis. exact (proj1 (Hpr b ltac:(lia))).
Qed.

(* a .rodata literal of the image (its bytes and NUL in the image, outside the statics and below g_nl; the rest of
   the NUL's granule, a registered global's redzone, is file-backed), at the cut *)
Lemma srm_lit_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc p s,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  srm_img_b p (p + Z.of_nat (length s) + 1) = true -> srm_nostatic_b p (p + Z.of_nat (length s) + 1) = true ->
  srm_rom_b p (p + Z.of_nat (length s) + 8) = true ->
  p + Z.of_nat (length s) + 8 <= LA_G_NL ->
  acstr_at SEGS (srm_m0 cx) p s -> astr_rt_ok SEGS (sm_regs cx) REAC_SERVED_MARK_AK (srm_m0 cx) p s ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) p s /\ astr_rt_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)) p s.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc p s Hpre Hb HX HKc Hib Hsb Hrb Hlt Hac Hrt.
  assert (Eown : as_owned_static B = Tfib_owned_static) by (destruct TB; assumption).
  assert (Eerr : as_errno B = TFIB_ERRNO) by (destruct TB; assumption).
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  pose proof asan_consts as ((C1a & C1b) & _). pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  assert (Hi : forall a, p <= a < p + Z.of_nat (length s) + 1 -> in_img SEGS a).
  { intros a Ha. rewrite HSEGS. exact (srm_img_of_b _ _ a Hib Ha). }
  assert (Hakb : forall a, p <= a < p + Z.of_nat (length s) + 1 ->
    akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a).
  { intros a Ha. right; right; left. split; [exact (Hi a Ha)|]. split.
    - rewrite Eown. exact (srm_nostatic_of_b _ _ a Hsb Ha).
    - rewrite Eerr. unfold TFIB_ERRNO, LA_G_NL in *. lia. }
  assert (Hv : forall a, p <= a < p + Z.of_nat (length s) + 1 ->
    aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a).
  { intros a Ha. apply (srm_view_kept SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb (Hakb a Ha)).
    apply (srm_img_notX SK B LAWS TB RELRO_IMG HSEGS cx X a Hpre HX (Hi a Ha)). unfold LA_G_NL in *. lia. }
  destruct Hrt as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  split.
  { apply (srm_acstr_move SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3)); [|exact Hac].
    intros x Hx. apply Hv. lia. }
  unfold astr_rt_ok. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  destruct (srm_shtr fx cx fpos X ly3 S3 W3 ms3 md3 p (Z.of_nat (length s) + 1) Hpre Hb HX ltac:(lia)
    ltac:(intros a Ha; apply Hakb; lia) R4 R5) as (Ra & Rh).
  split; [exact Ra|]. split; [exact Rh|].
  split.
  - intros b Hb1. change (ard SEGS (rdW W3 (ms_mem ms3)) b) with (aview SEGS (w_H W3) (ms_mem ms3) b).
    pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
    apply (srm_rom_vis p (p + Z.of_nat (length s) + 8) b (w_H W3) (ms_mem ms3) Hrb). lia.
  - unfold apart_frame. rewrite Hsp. left. unfold LA_G_NL in *. lia.
Qed.

Lemma srm_name_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc s,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  astr_arg SEGS (srm_m0 cx) (srm_name cx) (Some s) ->
  (forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
     akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a) ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (srm_name cx) s /\
  astr_rt_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)) (srm_name cx) s /\
  (length s <= 15)%nat /\
  apart_gnl LA_G_NL (srm_name cx) (Z.of_nat (length s) + 8) /\
  apart (sm_sink cx) AMF_BLOCK (srm_name cx) (Z.of_nat (length s) + 8) /\
  apart (as_errno B) 4 (srm_name cx) (Z.of_nat (length s) + 8) /\
  (srm_mk cx <> 0 -> apart (srm_name cx) (Z.of_nat (length s) + 8) (srm_mk cx) MK_SIZE).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc s Hpre Hb HX HKc Hs Hspan.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  pose proof asan_consts as ((C1a & C1b) & _). pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'.
  assert (Enm : pnm = Some s) by exact (astr_arg_unique SEGS _ _ _ _ P14 Hs).
  destruct (P15 s Enm) as (Hlen & Hrt & Hg & Hf & He & Hm).
  pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)) as Hmod.
  assert (Hv : forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
    aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a).
  { intros a Ha. apply (srm_view_kept SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb (Hspan a Ha)).
    intros HXa.
    destruct (srm_E_cases SK B LAWS TB RELRO_IMG HSEGS cx a Hpre (HX a HXa))
      as [Hr | (b & m & _ & Hr & [(-> & Hmk & ->) | (-> & ->)])].
    - unfold apart_gnl in Hg. unfold srm_name in *. unfold NK_N_SENT, NK_SIZE in *. lia.
    - specialize (Hm Hmk). unfold apart in Hm. assert (Rq : req_size MK_SIZE = MK_SIZE) by reflexivity.
      rewrite Rq in Hr. unfold srm_name, srm_mk in *. lia.
    - unfold apart in Hf. assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
      rewrite Rq in Hr. unfold srm_name in *. lia. }
  destruct Hrt as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  split.
  { apply (srm_acstr_move SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3)); [|exact (proj2 Hs)].
    intros x Hx. apply Hv. lia. }
  split.
  { unfold astr_rt_ok. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
    destruct (srm_shtr fx cx fpos X ly3 S3 W3 ms3 md3 (srm_name cx) (Z.of_nat (length s) + 1) Hpre Hb HX
      ltac:(lia) ltac:(intros a Ha; apply Hspan; lia) R4 R5) as (Ra & Rh).
    split; [exact Ra|]. split; [exact Rh|].
    split.
    - intros b Hb1. change (ard SEGS (rdW W3 (ms_mem ms3)) b) with (aview SEGS (w_H W3) (ms_mem ms3) b).
      exact (srm_tail_vis fx cx fpos X ly3 S3 W3 ms3 md3 (srm_name cx + Z.of_nat (length s)) b Hpre Hb
        (Hspan (srm_name cx + Z.of_nat (length s)) ltac:(lia)) ltac:(lia) (R6 b Hb1)).
    - unfold apart_frame in *. rewrite Hsp. unfold srm_name, srm_sp in *. lia. }
  split; [exact Hlen|]. split; [exact Hg|]. split; [exact Hf|]. split; [exact He | exact Hm].
Qed.

(* a live interface-table string at the entry, from the cut's pointer cell *)
Lemma srm_table_entry : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 kbs tab i n2 ix p,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  amk_nlk_ok SEGS (srm_m0 cx) kbs tab 2 -> nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\ p <> 0 /\
  acstr_at SEGS (srm_m0 cx) p n2 /\
  astr_rt_ok SEGS (sm_regs cx) REAC_SERVED_MARK_AK (srm_m0 cx) p n2 /\
  apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1) /\
  apart (as_errno B) 4 p (Z.of_nat (length n2) + 1) /\
  apart (sm_sink cx) AMF_BLOCK p (Z.of_nat (length n2) + 1) /\
  (srm_mk cx <> 0 -> apart (srm_mk cx) MK_SIZE p (Z.of_nat (length n2) + 1)).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 kbs tab i n2 ix p Hpre Hb HX Hnlk Hnth Hau Hp.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'.
  destruct Hnlk as (Hn1 & _ & _ & _ & _ & Htab & _).
  destruct P3 as (Hp1 & _ & _ & _ & _ & Hptab & _).
  pose proof (anlk_at_unique SEGS _ _ _ _ Hn1 Hp1) as Ek. subst pkbs.
  pose proof (aiftab_at_unique SEGS _ _ _ _ Htab Hptab) as Et. subst ptab.
  pose proof Htab as (_ & Hlen & Hent).
  assert (Hi : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  assert (Hau0 : au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { unfold srm_m0. apply (srm_val_mem_move SEGS (w_H W3) (w_H (sm_W cx)) (ms_mem ms3) (sm_memc cx)); [|exact Hau].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. symmetry.
    apply (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 x Hpre Hb HX).
    unfold NK_IF_NAME, NK_SIZE in *. lia. }
  destruct (Hent i n2 ix Hnth) as (_ & p' & Hp' & Hp'0 & Hc' & _).
  pose proof (srm_au64_unique SEGS _ _ _ _ Hp' Hau0) as Ep.
  pose proof (srm_acstr_range SEGS _ _ _ Hc') as Hr'.
  rewrite !Z.mod_small in Ep by lia. subst p'.
  destruct (P7 i n2 ix p Hnth Hau0 Hp) as (Hrt & Hg & He & Hf & Hm).
  split; [exact Hau0|]. split; [exact Hp'0|]. split; [exact Hc'|]. split; [exact Hrt|].
  split; [exact Hg|]. split; [exact He|]. split; [exact Hf | exact Hm].
Qed.

Lemma srm_table_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc kbs tab i n2 ix p,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  amk_nlk_ok SEGS (srm_m0 cx) kbs tab 2 ->
  nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  (forall a, p <= a <= p + Z.of_nat (length n2) ->
     akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a) ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) p n2 /\
  astr_rt_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)) p n2 /\
  achk SEGS (rdW W3 (ms_mem ms3)) p (Z.of_nat (length n2) + 1) /\
  apart_frame (sm_regs cx) REAC_SERVED_MARK_AK p (Z.of_nat (length n2) + 1) /\
  apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1) /\
  apart (as_errno B) 4 p (Z.of_nat (length n2) + 1) /\
  apart (sm_sink cx) AMF_BLOCK p (Z.of_nat (length n2) + 1) /\
  (srm_mk cx <> 0 -> apart (srm_mk cx) MK_SIZE p (Z.of_nat (length n2) + 1)).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc kbs tab i n2 ix p Hpre Hb HX HKc Hnlk Hnth Hau Hp Hspan.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  pose proof asan_consts as ((C1a & C1b) & _). pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  destruct (srm_table_entry fx cx fpos X ly3 S3 W3 ms3 md3 kbs tab i n2 ix p Hpre Hb HX Hnlk Hnth Hau Hp)
    as (Hau0 & Hp0 & Hc & Hrt & Hg & He & Hf & Hm).
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length n2)) 8 ltac:(lia)) as Hmod.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'.
  pose proof A1 as (_ & _ & (memS & HJ & _) & _). destruct HJ as (HARc & _).
  assert (Hv : forall a, p <= a <= p + Z.of_nat (length n2) ->
    aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a).
  { intros a Ha. apply (srm_view_kept SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb (Hspan a Ha)).
    intros HXa.
    destruct (srm_E_cases SK B LAWS TB RELRO_IMG HSEGS cx a Hpre (HX a HXa))
      as [Hr | (b & m & Hbm & Hr & [(-> & Hmk & ->) | (-> & ->)])].
    - unfold apart_gnl in Hg. unfold NK_N_SENT, NK_SIZE, LA_G_NL in *. lia.
    - specialize (Hm Hmk). unfold apart in Hm. assert (Rq : req_size MK_SIZE = MK_SIZE) by reflexivity.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hbm) as (Hal & _).
      rewrite Rq in Hr. unfold srm_mk in *. unfold MK_SIZE in *. lia.
    - unfold apart in Hf. assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hbm) as (Hal & _).
      rewrite Rq in Hr. unfold AMF_BLOCK in *. lia. }
  destruct Hrt as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  destruct (srm_shtr fx cx fpos X ly3 S3 W3 ms3 md3 p (Z.of_nat (length n2) + 1) Hpre Hb HX
    ltac:(lia) ltac:(intros a Ha; apply Hspan; lia) R4 R5) as (Ra & Rh).
  split.
  { apply (srm_acstr_move SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3)); [|exact Hc].
    intros x Hx. apply Hv. lia. }
  split.
  { unfold astr_rt_ok. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
    split; [exact Ra|]. split; [exact Rh|].
    split.
    - intros b Hb1. change (ard SEGS (rdW W3 (ms_mem ms3)) b) with (aview SEGS (w_H W3) (ms_mem ms3) b).
      exact (srm_tail_vis fx cx fpos X ly3 S3 W3 ms3 md3 (p + Z.of_nat (length n2)) b Hpre Hb
        (Hspan (p + Z.of_nat (length n2)) ltac:(lia)) ltac:(lia) (R6 b Hb1)).
    - unfold apart_frame in *. rewrite Hsp. unfold srm_sp in *. lia. }
  split.
  { unfold achk. split; [unfold amem_range in *; lia|]. split; [exact Ra | exact Rh]. }
  split; [exact R7|]. split; [exact Hg|]. split; [exact He|]. split; [exact Hf | exact Hm].
Qed.

Lemma srm_policy_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  amk_policy_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc Hpre Hb HX HKc.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'.
  destruct P8 as (L1 & T1 & L2 & T2 & L3 & T3 & L4 & T4 & L5 & T5 & L6 & T6 & L7 & T7 & L8 & T8 & L9 & T9
                  & L10 & T10 & L11 & T11 & L12 & T12 & L13 & T13).
  unfold amk_policy_ok.
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_RSD_PREFIX S_PREFIX Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L1 T1) as (N1 & U1).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_RSD_VLAN S_VLAN Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L2 T2) as (N2 & U2).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_SERVED S_SERVED Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L3 T3) as (N3 & U3).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_FMT_S S_FMT_S Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L4 T4) as (N4 & U4).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_FMT_SS S_FMT_SS Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L5 T5) as (N5 & U5).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_REACPW S_REACPW Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L6 T6) as (N6 & U6).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_E_NOT_MARKED S_E_NOT_MARKED Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L7 T7) as (N7 & U7).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_READERR S_STR3 Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L8 T8) as (N8 & U8).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_WRITEERR S_STR5 Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L9 T9) as (N9 & U9).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_VLANLINE S_STR8 Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L10 T10) as (N10 & U10).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_OWNALIAS S_STR9 Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L11 T11) as (N11 & U11).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_NOCAP S_STR6 Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L12 T12) as (N12 & U12).
  destruct (srm_lit_at fx cx fpos X ly3 S3 W3 ms3 md3 Kc LA_S_EMPTY [] Hpre Hb HX HKc
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(apply Z.leb_le; vm_compute; reflexivity)
    L13 T13) as (N13 & U13).
  refine (conj N1 (conj U1 _)). refine (conj N2 (conj U2 _)). refine (conj N3 (conj U3 _)).
  refine (conj N4 (conj U4 _)). refine (conj N5 (conj U5 _)). refine (conj N6 (conj U6 _)).
  refine (conj N7 (conj U7 _)). refine (conj N8 (conj U8 _)). refine (conj N9 (conj U9 _)).
  refine (conj N10 (conj U10 _)). refine (conj N11 (conj U11 _)). refine (conj N12 (conj U12 _)).
  exact (conj N13 U13).
Qed.

Lemma srm_errno_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  as_errno B = as_tp B - 164 /\ awrange SEGS (rdW W3 (ms_mem ms3)) (as_errno B) 4 /\
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF (as_errno B) 4 /\
  shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms3))) (as_errno B) 4 /\
  apart_frame (ms_regs ms3) Kc (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4 /\
  apart (as_errno B) 4 (sm_sink cx) AMF_BLOCK /\
  (srm_mk cx <> 0 -> apart (as_errno B) 4 (srm_mk cx) MK_SIZE) /\
  apart (as_errno B) 4 LA_G_SAY 8 /\ apart (as_errno B) 4 LA_G_SAID SAID_SIZE.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc Hpre Hb HKc.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  destruct (srm_lyeq SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (_ & _ & _ & _ & HAR3).
  pose proof asan_consts as ((C1a & C1b) & _). pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  assert (Eerr : as_errno B = TFIB_ERRNO) by (destruct TB; assumption).
  pose proof Hpre as Hpre'. srm_unpreA Hpre'.
  destruct P4 as (E1 & _ & _ & _ & E5 & E6 & E7).
  assert (HZ : range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF (as_errno B) 4 /\
               shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms3))) (as_errno B) 4)
    by (eapply zsh_errno_ard; eassumption).
  split; [exact E1|].
  split.
  { intros i Hi. generalize (rdW W3 (ms_mem ms3)) as mm. intros mm. rewrite HSEGS, Eerr.
    apply (writable_at_of_wseg tfibsegs mm TFIB_ERRNO 4).
    - unfold TFIB_ERRNO. lia.
    - apply Z.leb_le. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - lia. }
  split; [exact (proj1 HZ)|]. split; [exact (proj2 HZ)|].
  split; [unfold apart_frame; rewrite Hsp, Eerr; left; unfold TFIB_ERRNO, srm_sp in *; lia|].
  split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact P5 | exact P6].
Qed.

Lemma srm_gnl_sh_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  range_addressable (ard SEGS (rdW W3 (ms_mem ms3))) SHADOW_OFF LA_G_NL NK_SIZE /\
  shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms3))) LA_G_NL NK_SIZE.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Hb. srm_unbaseA Hb.
  pose proof B6 as (_ & _ & (memS & HJ & _) & _). destruct HJ as (HAR3 & _).
  eapply zsh_gnl_ard; eassumption.
Qed.

Lemma srm_marks_blk_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK -> srm_mk cx <> 0 ->
  amarks_blk_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)) (srm_mk cx) /\
  amarks_ledger (ablocks B ly3 S3) (srm_mk cx) /\
  apart_gnl LA_G_NL (srm_mk cx) MK_SIZE /\ apart (as_errno B) 4 (srm_mk cx) MK_SIZE /\
  apart (sm_sink cx) AMF_BLOCK (srm_mk cx) MK_SIZE.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc Hpre Hb HX HKc Hmk.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  destruct (srm_lyeq SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (_ & _ & _ & _ & HAR3).
  pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'. pose proof Hb as Hb'. srm_unbaseA Hb'.
  destruct (P16 Hmk) as ((M1 & M2 & M3 & M4 & M5 & M6) & Mg & Me & Mf & _).
  destruct (P2 Hmk) as (Hl & Htop).
  assert (Hl3 : In (srm_mk cx, MK_SIZE) (ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact B10 | exact Hl]. }
  assert (Rq : req_size MK_SIZE = MK_SIZE) by reflexivity.
  destruct (srm_shtr fx cx fpos X ly3 S3 W3 ms3 md3 (srm_mk cx) MK_SIZE Hpre Hb HX ltac:(unfold MK_SIZE; lia)
    ltac:(intros a Ha; right; left; exists (srm_mk cx), MK_SIZE; split; [exact Hl | rewrite Rq; exact Ha])
    M3 M4) as (Ra & Rh).
  split.
  { split; [exact M1|]. split; [exact M2|]. split; [exact Ra|]. split; [exact Rh|]. split.
    - intros b Hb1. change (ard SEGS (rdW W3 (ms_mem ms3)) b) with (aview SEGS (w_H W3) (ms_mem ms3) b).
      apply (srm_blk_tail_vis16 SEGS B ly3 S3 W3 (ms_mem ms3) md3 (srm_mk cx) MK_SIZE b HAR3 Hl3).
      assert (Ru : round_up MK_SIZE 16 = 528) by reflexivity. rewrite Ru. unfold MK_SIZE in *. lia.
    - unfold apart_frame in *. rewrite Hsp. unfold srm_sp, srm_mk in *. lia. }
  split; [split; [exact Hl3 | exact Htop]|].
  split; [exact Mg|]. split; [exact Me | exact Mf].
Qed.

Lemma srm_file_blk_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  amf_blk_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)) (sm_sink cx) /\
  In (sm_sink cx, AMF_BLOCK) (ablocks B ly3 S3).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc Hpre Hb HX HKc.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  pose proof Hpre as Hpre'. srm_unpreA Hpre'. pose proof Hb as Hb'. srm_unbaseA Hb'.
  destruct P13 as (F1 & F2 & F3 & F4).
  assert (Hl3 : In (sm_sink cx, AMF_BLOCK) (ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact B10 | exact P1]. }
  assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
  destruct (srm_shtr fx cx fpos X ly3 S3 W3 ms3 md3 (sm_sink cx) AMF_BLOCK Hpre Hb HX ltac:(unfold AMF_BLOCK; lia)
    ltac:(intros a Ha; right; left; exists (sm_sink cx), AMF_BLOCK; split; [exact P1 | rewrite Rq; exact Ha])
    F2 F3) as (Ra & Rh).
  split; [|exact Hl3].
  split; [exact F1|]. split; [exact Ra|]. split; [exact Rh|].
  unfold apart_frame in *. rewrite Hsp. unfold srm_sp in *. lia.
Qed.
End k.
