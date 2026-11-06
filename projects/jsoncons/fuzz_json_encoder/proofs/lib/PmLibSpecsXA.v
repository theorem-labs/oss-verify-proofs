(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMXA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KEY_STATES : list Z := [PML.ST_EXPECT_MEMBER_NAME_OR_END; PML.ST_EXPECT_MEMBER_NAME; PML.ST_EXPECT_COLON].
Definition key_inv (ps : PML.pstate) : Prop :=
  PML.ps_more ps = true -> (In (PML.ps_st ps) KEY_STATES \/ (exists x, In x (PML.ps_stack ps) /\ In x (PML.ST_MEMBER_NAME :: KEY_STATES))) -> 1 <= PML.ps_level ps.
Lemma key_inv_pos : forall ps, 1 <= PML.ps_level ps -> key_inv ps.
Proof. intros ps H _ _. exact H. Qed.
Lemma key_inv_stopped : forall ps, PML.ps_more ps = false -> key_inv ps.
Proof. intros ps H Hm. rewrite H in Hm. discriminate Hm. Qed.
Lemma key_inv_same : forall ps ps', PML.ps_st ps' = PML.ps_st ps -> PML.ps_stack ps' = PML.ps_stack ps -> PML.ps_level ps' = PML.ps_level ps -> PML.ps_more ps = true -> key_inv ps -> key_inv ps'.
Proof. intros ps ps' H1 H2 H3 H4 K Hm Hx. rewrite H1, H2, H3 in *. exact (K H4 Hx). Qed.
(* [comment removed for export] *)
Lemma key_inv_plain : forall ps, PML.wf_ps ps -> PML.ps_more ps = true -> ~ In (PML.ps_st ps) KEY_STATES -> ~ PML.comment_or_cr (PML.ps_st ps) -> PML.ps_st ps <> PML.ST_STRING -> key_inv ps.
Proof.
  intros ps HW Hm Hk Hc Hs _ [Hx|(x & Hin & Hx)]; [exact (False_ind _ (Hk Hx))|]. exfalso.
  destruct HW as (_ & _ & _ & _ & C & T & Hstk & HC & HM). destruct (HM Hm) as (_ & _ & _ & HT & _).
  assert (HT0 : T = []).
  { destruct HT as [[-> _]|[[-> Hst]|[(S & _ & -> & Hcc)|(S & _ & -> & Hst)]]]; [reflexivity | exact (False_ind _ (Hs Hst)) | exact (False_ind _ (Hc Hcc)) | exfalso; apply Hc; rewrite Hst; right; reflexivity]. }
  rewrite HT0, app_nil_r in Hstk. rewrite Hstk in Hin. destruct Hin as [<-|Hin].
  - unfold PML.ST_ROOT, PML.ST_MEMBER_NAME, KEY_STATES, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in Hx. cbn in Hx. lia.
  - pose proof (proj1 (Forall_forall _ _) HC x Hin) as Hcx. unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hcx.
    unfold PML.ST_MEMBER_NAME, KEY_STATES, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in Hx. cbn in Hx. lia.
Qed.
(* [comment removed for export] *)
Lemma key_inv_setwin : forall ps w, key_inv ps -> key_inv (PML.ps_set_win ps w).
Proof. intros ps w H. destruct ps. exact H. Qed.
Lemma key_inv_setnst : forall ps n, key_inv ps -> key_inv (PML.ps_set_nst ps n).
Proof. intros ps n H. destruct ps. exact H. Qed.
(* [comment removed for export] *)
Definition key_ok (ps : PML.pstate) : Prop := forall rest, PML.ps_stack ps = rest ++ [PML.ST_MEMBER_NAME] -> 1 <= PML.ps_level ps.
Lemma key_ok_of_inv : forall ps, key_inv ps -> PML.ps_more ps = true -> key_ok ps.
Proof. intros ps K Hm rest Hs. apply (K Hm). right. exists PML.ST_MEMBER_NAME. split; [rewrite Hs; apply in_or_app; right; left; reflexivity | left; reflexivity]. Qed.
(* [comment removed for export] *)
Lemma key_inv_push : forall ps ps' x, PML.ps_more ps = true -> PML.ps_stack ps' = PML.ps_stack ps ++ [x] -> PML.ps_level ps' = PML.ps_level ps -> key_inv ps ->
  (In (PML.ps_st ps') KEY_STATES \/ In x (PML.ST_MEMBER_NAME :: KEY_STATES) -> In (PML.ps_st ps) KEY_STATES \/ 1 <= PML.ps_level ps) -> key_inv ps'.
Proof.
  intros ps ps' x Hm Hs Hl K Himp Hm' [Hst|(y & Hin & Hy)]; rewrite Hl.
  - destruct (Himp (or_introl Hst)) as [H|H]; [exact (K Hm (or_introl H)) | exact H].
  - rewrite Hs in Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
    + exact (K Hm (or_intror (ex_intro _ y (conj Hin Hy)))).
    + destruct (Himp (or_intror Hy)) as [H|H]; [exact (K Hm (or_introl H)) | exact H].
Qed.
(* [comment removed for export] *)
Lemma key_inv_pop : forall ps ps' x, PML.ps_more ps = true -> PML.ps_stack ps = PML.ps_stack ps' ++ [x] -> PML.ps_level ps' = PML.ps_level ps -> key_inv ps ->
  (In (PML.ps_st ps') KEY_STATES -> In (PML.ps_st ps) KEY_STATES \/ In x KEY_STATES \/ 1 <= PML.ps_level ps) -> key_inv ps'.
Proof.
  intros ps ps' x Hm Hs Hl K Himp Hm' [Hst|(y & Hin & Hy)]; rewrite Hl.
  - destruct (Himp Hst) as [H|[H|H]]; [exact (K Hm (or_introl H)) | | exact H].
    apply (K Hm). right. exists x. split; [rewrite Hs; apply in_or_app; right; left; reflexivity | right; exact H].
  - apply (K Hm). right. exists y. split; [rewrite Hs; apply in_or_app; left; exact Hin | exact Hy].
Qed.
(* [comment removed for export] *)
Lemma key_inv_sub : forall ps ps', PML.ps_more ps = true -> key_inv ps -> (forall x, In x (PML.ps_stack ps') -> In x (PML.ps_stack ps)) -> PML.ps_level ps' = PML.ps_level ps ->
  (PML.ps_more ps' = true -> In (PML.ps_st ps') KEY_STATES -> 1 <= PML.ps_level ps) -> key_inv ps'.
Proof.
  intros ps ps' Hm K Hsub Hl Hst Hm' [Hin|(x & Hin & Hx)]; rewrite Hl; [exact (Hst Hm' Hin)|]. apply (K Hm). right. exists x. exact (conj (Hsub x Hin) Hx).
Qed.
(* [comment removed for export] *)
Lemma key_inv_cont : forall ps C, PML.ps_stack ps = PML.ST_ROOT :: C -> Forall PML.is_container C -> (PML.ps_more ps = true -> In (PML.ps_st ps) KEY_STATES -> 1 <= PML.ps_level ps) -> key_inv ps.
Proof.
  intros ps C Hs HC Hst Hm [Hin|(x & Hin & Hx)]; [exact (Hst Hm Hin)|]. exfalso. rewrite Hs in Hin. destruct Hin as [<-|Hin].
  - unfold PML.ST_ROOT, PML.ST_MEMBER_NAME, KEY_STATES, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in Hx. cbn in Hx. lia.
  - pose proof (proj1 (Forall_forall _ _) HC x Hin) as Hcx. unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hcx.
    unfold PML.ST_MEMBER_NAME, KEY_STATES, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in Hx. cbn in Hx. lia.
Qed.
(* [comment removed for export] *)
Lemma key_inv_init : forall sb bptr, key_inv (PMS.ps_init sb bptr).
Proof.
  intros sb bptr _ [H|(x & H & Hx)]; cbn in H.
  - unfold PML.ST_START, KEY_STATES, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in H. cbn in H. exfalso. lia.
  - destruct H as [<-|[]]. unfold PML.ST_ROOT, PML.ST_MEMBER_NAME, KEY_STATES, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON in Hx. cbn in Hx. exfalso. lia.
Qed.

(* [comment removed for export] *)
Section SpecsXA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
(* [comment removed for export] *)
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Variable VIS_SCRA : Z.              (* [comment removed for export] *)
Variable VIS_D : Z.                 (* [comment removed for export] *)
Variable benc : PMES.eghost -> Z.   (* [comment removed for export] *)
Variable eroomA : PMES.eghost -> PMES.eev -> Prop.   (* [comment removed for export] *)

Abbreviation cps_asan := (PMSA.cps_asan L ar HI).
Abbreviation pstate := PML.pstate.   Abbreviation mem := PMSA.mem.
(* [comment removed for export] *)
Abbreviation std_args := PMSA.std_args.   Abbreviation cur_args := PMSA.cur_args.   Abbreviation literal_rel := PMSA.literal_rel.   Abbreviation win_exhausted := PMSA.win_exhausted.
Abbreviation not_retreated := PMSA.not_retreated.   Abbreviation PF_SCR := PMSA.PF_SCR.   Abbreviation ENDNUM_SCR := PMSA.ENDNUM_SCR.   Abbreviation ESV_SCR := PMSA.ESV_SCR.
Abbreviation PSOME_SCR := PMSA.PSOME_SCR.   Abbreviation text_inA := PMSA.text_inA.   Abbreviation ec_at := (PMSA.ec_at L IC).   Abbreviation vis_at := (PMSA.vis_at L IC).
Abbreviation parser_at := (PMSA.parser_at L IC).   Abbreviation parser_sh := PMSA.parser_sh.   Abbreviation win_okA := PMSA.win_okA.   Abbreviation buf_bound_stale := PMSA.buf_bound_stale.
Abbreviation stksh := (PMSA.stksh ar).   Abbreviation fobj := PMSA.fobj.   Abbreviation a0 := PMSA.a0.   Abbreviation a1 := PMSA.a1.   Abbreviation a2 := PMSA.a2.   Abbreviation a3 := PMSA.a3.
Abbreviation a4 := PMSA.a4.   Abbreviation consumed := PMSA.consumed.   Abbreviation u8 := (PMSA.u8 L).   Abbreviation u32 := (PMSA.u32 L).   Abbreviation u64 := (PMSA.u64 L).   Abbreviation W_parE := (PMSA.W_parE L IC).   Abbreviation ls_ok := (PMSA.ls_ok L IC).
Definition lits_ok (M : PMSA.mem) : Prop := PMLA.lits_ok (hl_segs L) IC M.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kenc (eg : PMES.eghost) : Z := (PMES.kv_s2 (PMES.g_rep eg) + PMES.kv_st (PMES.g_scap eg)) * hl_k_per_malloc L.
(* [comment removed for export] *)
Definition enc_sync (ps : pstate) (eg : PMES.eghost) : Prop := PMES.depth (PMES.g_es eg) = PML.ps_level ps /\ key_inv ps.
(* [comment removed for export] *)
Definition W_encA (V S2 : Z) : list L5.range := [(V + PMES.O_STACK, 40); (V + PMES.O_DEPTH, 4); (S2, 24); (PMLA.LIT_LO IC, PMLA.LIT_HI IC - PMLA.LIT_LO IC)].
Definition W_parxA (P V E S2 : Z) : list L5.range := PMLA.W_parA IC P E ++ W_encA V S2.
Definition W_parxeA (P V E S2 : Z) : list L5.range := W_parE P E ++ W_encA V S2.
(* [comment removed for export] *)
Definition ecreditA (cr : credit) (g : PMES.eghost) (kx bx : Z) : Prop := 0 <= kx /\ kenc g <= fst cr - kx /\ 0 <= bx /\ benc g <= snd cr - bx.
(* [comment removed for export] *)
Definition pbytes (ps : pstate) : Z :=
  hl_b_lin L * ((2 ^ 28 - 2 * PML.ps_bcap ps) + (2112 - 2 * PML.ps_scap ps)) + (Z.log2 (2 ^ 27 / PML.ps_bcap ps) + Z.log2 (1056 / PML.ps_scap ps)) * hl_b_overhead L.
(* [comment removed for export] *)
Lemma ecredit_of_px : forall cr ps eg kx bx, PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) -> 0 <= kx -> 0 <= bx -> 0 <= kenc eg -> 0 <= benc eg ->
  0 <= PML.kleft ps * hl_k_per_malloc L -> 0 <= pbytes ps ->
  ecreditA cr eg (kx + PML.kleft ps * hl_k_per_malloc L) (bx + pbytes ps).
Proof.
  unfold PMLA.pcredit_xA, PMLA.pcreditA, ecreditA, pbytes, PML.bleft, PML.kleft. cbn [fst snd]. intros cr ps eg kx bx (H0 & H1 & H2 & H3 & H4) Hk Hb He Hbe Hp Hq. repeat split; lia.
Qed.
Lemma px_of_ecredit : forall cr cr' ps eg eg' kx bx, PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) -> 0 <= kx -> 0 <= bx -> 0 <= kenc eg' -> 0 <= benc eg' ->
  ecreditA cr' eg' (kx + PML.kleft ps * hl_k_per_malloc L) (bx + pbytes ps) ->
  PMLA.pcredit_xA L cr' ps (kx + kenc eg') (bx + benc eg').
Proof.
  unfold PMLA.pcredit_xA, PMLA.pcreditA, ecreditA, pbytes, PML.bleft, PML.kleft. cbn [fst snd]. intros cr cr' ps eg eg' kx bx (H0 & H1 & H2 & H3 & H4) Hk Hb He Hbe (E0 & E1 & E2 & E3).
  split; [lia|]. split; [lia|]. split; [exact H2|]. split; lia.
Qed.
Lemma kenc_nonneg : forall eg, 0 <= hl_k_per_malloc L -> 0 <= kenc eg.
Proof.
  intros eg Hk. unfold kenc, PMES.kv_s2, PMES.kv_st.
  assert (A1 : 0 <= match PMES.g_rep eg with PML.SShort _ => 43 | PML.SLong cap _ _ => 1 + Z.log2 (2 ^ 47 / cap) end).
  { destruct (PMES.g_rep eg) as [|cap p cs]; [lia | pose proof (Z.log2_nonneg (2 ^ 47 / cap)); lia]. }
  assert (A2 : 0 <= (if PMES.g_scap eg =? 0 then 11 else Z.log2 (32768 / PMES.g_scap eg))).
  { destruct (PMES.g_scap eg =? 0); [lia | apply Z.log2_nonneg]. }
  nia.
Qed.
(* [comment removed for export] *)
Definition efootA (V S2 : Z) (g : PMES.eghost) (a : Z) : Prop :=
  (V <= a < V + PMES.ENC_SIZE) \/ (S2 <= a < S2 + 24) \/ in_block (PMES.g_lbv g) a \/ (exists b, In b (PMES.g_lbv g) /\ in_shadow_of (fst b) (snd b) a) \/
  in_shadow_of V PMES.ENC_SIZE a \/ in_shadow_of S2 24 a.
Definition enc_agreeP : Prop :=
  forall (M M' : mem) V S2 g, enc_invA M V S2 g -> (forall a, efootA V S2 g a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> enc_invA M' V S2 g.
(* [comment removed for export] *)
Definition bencP : Prop := forall g, 0 <= benc g.
(* [comment removed for export] *)
Definition ev_small (ev : PMES.eev) : Prop := match ev with PMES.EvKey bs | PMES.EvStr _ bs => PMES.len bs < 2 ^ 27 | _ => True end.
Definition roomxP : Prop := forall (M : mem) V S2 g ev, enc_invA M V S2 g -> ev_small ev -> eroomA g ev.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vtransA (pc : Z) (ev : PMES.eev) (Args : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : PMES.eghost),
    cps_asan pc r sp VIS_SCRA (LBo ++ PMES.g_lbv g) FF LK cr A VIS_D
      (fun R M => PMSA.a0 R V /\ Args LBo FF sp V S2 R M /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp VIS_SCRA /\ enc_invA M V S2 g /\ PMES.ev_guard (PMES.g_es g) ev /\ eroomA g ev /\
                  PMLA.img_ro IC M /\ lits_ok M /\ ecreditA cr g kx bx /\ PMSA.fobj M FF V PMES.ENC_SIZE /\ PMSA.fobj M FF S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24)
      (fun R M R' M' LB' cr' LBk W => exists (g' : PMES.eghost) (pay : Z),
          PMSA.a0 R' 1 /\ enc_invA M' V S2 g' /\ PMES.g_es g' = PMES.estep (PMES.g_es g) ev /\ PMES.pay_ok ev pay /\
          PMES.g_len g' = PMES.g_len g + PMES.ev_ind (PMES.g_es g) ev + pay /\
          lits_ok M' /\ LB' = LBo ++ PMES.g_lbv g' /\ LBk = LBo /\ W = W_encA V S2 /\ ecreditA cr' g' kx bx).
(* [comment removed for export] *)
Definition vtranseA (pc : Z) (ev : PMES.eev) (Args : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : PMES.eghost),
    cps_asan pc r sp VIS_SCRA (LBo ++ PMES.g_lbv g) FF LK cr A VIS_D
      (fun R M => PMSA.a0 R V /\ Args LBo FF sp V S2 R M /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp VIS_SCRA /\ enc_invA M V S2 g /\ PMES.ev_guard (PMES.g_es g) ev /\ eroomA g ev /\
                  PMLA.img_ro IC M /\ lits_ok M /\ ecreditA cr g kx bx /\ PMSA.fobj M FF V PMES.ENC_SIZE /\ PMSA.fobj M FF S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24)
      (fun R M R' M' LB' cr' LBk W => exists (g' : PMES.eghost) (pay : Z),
          PMSA.a0 R' 1 /\ enc_invA M' V S2 g' /\ PMES.g_es g' = PMES.estep (PMES.g_es g) ev /\ PMES.pay_ok ev pay /\
          PMES.g_len g' = PMES.g_len g + PMES.ev_ind (PMES.g_es g) ev + pay /\
          lits_ok M' /\ LB' = LBo ++ PMES.g_lbv g' /\ LBk = LBo /\ W = W_encA V S2 ++ [(hl_tp L - 164, 4)] /\ ecreditA cr' g' kx bx).
(* [comment removed for export] *)
Definition sv_argA (LBo : list (Z * Z)) (FF : list fframe) (sp V S2 : Z) (M : mem) (sv : Z) (bs : list Z) : Prop :=
  exists q, u64 M sv q /\ u64 M (sv + 8) (PMES.len bs) /\ L5.bytes_at (hl_segs L) M q bs /\ L5.defined M q (PMES.len bs) /\ text_inA M LBo q (PMES.len bs) /\
            PMLA.apart sv 16 V PMES.ENC_SIZE /\ PMLA.apart sv 16 S2 24 /\ fobj M FF sv 16.
Definition argT : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop := fun _ _ _ _ _ _ _ => True.
(* [comment removed for export] *)
Definition visit_begin_object_specXA (pc : Z) : Prop := vtransA pc (PMES.EvBegin false) argT.
Definition visit_begin_array_specXA (pc : Z) : Prop := vtransA pc (PMES.EvBegin true) argT.
Definition visit_end_object_specXA (pc : Z) : Prop := vtransA pc PMES.EvEnd argT.
Definition visit_end_array_specXA (pc : Z) : Prop := vtransA pc PMES.EvEnd argT.
Definition visit_null_specXA (pc : Z) : Prop := vtransA pc PMES.EvNull argT.
Definition visit_bool_specXA (pc : Z) : Prop := forall (b : bool), vtransA pc (PMES.EvBool b) (fun _ _ _ _ _ R _ => a1 R (PML.b2z b)).
Definition visit_uint64_specXA (pc : Z) : Prop := forall (v : Z), vtransA pc PMES.EvU64 (fun _ _ _ _ _ R _ => a1 R v /\ 0 <= v < 2 ^ 64).
Definition visit_int64_specXA (pc : Z) : Prop := forall (v : Z), vtransA pc PMES.EvI64 (fun _ _ _ _ _ R _ => a1 R v /\ 0 <= v < 2 ^ 64).
Definition visit_double_specXA (pc : Z) : Prop := vtranseA pc PMES.EvDbl argT.      (* [comment removed for export] *)
Definition visit_key_specXA (pc : Z) : Prop := forall (bs : list Z) (sv : Z), vtransA pc (PMES.EvKey bs) (fun LBo FF sp V S2 R M => a1 R sv /\ sv_argA LBo FF sp V S2 M sv bs).
Definition visit_string_specXA (pc : Z) : Prop := forall (tag : Z) (bs : list Z) (sv : Z), 0 <= tag < 256 ->
  vtransA pc (PMES.EvStr tag bs) (fun LBo FF sp V S2 R M => a1 R sv /\ a2 R tag /\ sv_argA LBo FF sp V S2 M sv bs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PFXA_SCR : Z := Z.max PF_SCR (512 + VIS_SCRA).                (* [comment removed for export] *)
Definition ESVXA_SCR : Z := Z.max ESV_SCR (160 + VIS_SCRA).
Definition ENDNUMXA_SCR : Z := Z.max ENDNUM_SCR (160 + VIS_SCRA).
Definition PSOMEXA_SCR : Z := 704 + PFXA_SCR.
Definition READNEXTXA_SCR : Z := 224 + PSOMEXA_SCR.
Definition READXA_SCR : Z := 32 + READNEXTXA_SCR.
Definition DVXA2 : Z := Z.max 2 (1 + VIS_D).                               (* [comment removed for export] *)
Definition DVXA3 : Z := Z.max 3 (1 + VIS_D).                               (* [comment removed for export] *)
Definition DVXA4 : Z := Z.max 4 (1 + VIS_D).                               (* [comment removed for export] *)
Definition DBEGXA : Z := Z.max 5 (1 + VIS_D).                              (* [comment removed for export] *)
Definition DPSXA : Z := Z.max 4 (2 + VIS_D).                               (* [comment removed for export] *)
Definition DPNXA : Z := Z.max 5 (2 + VIS_D).                               (* [comment removed for export] *)
Definition DPSOMEXA : Z := Z.max 6 (3 + VIS_D).                            (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ptrans_gbxA (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : pstate) (eg : PMES.eghost),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) FF LK cr A d                                        (* [comment removed for export] *)
      (fun R M => Args R M LBo P V E ps eg /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  enc_invA M V S2 eg /\ lits_ok M /\ enc_sync ps eg /\                                                                (* [comment removed for export] *)
                  0 <= kx /\ 0 <= bx /\ PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) /\                                      (* [comment removed for export] *)
                  fobj M FF P 272 /\ fobj M FF V PMES.ENC_SIZE /\ fobj M FF E 16 /\ fobj M FF S2 24 /\                         (* [comment removed for export] *)
                  PMLA.apart P 272 V PMES.ENC_SIZE /\ PMLA.apart P 272 E 16 /\ PMLA.apart V PMES.ENC_SIZE E 16 /\
                  PMLA.apart P 272 S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24 /\ PMLA.apart S2 24 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          enc_invA M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> enc_sync ps' eg') /\                                             (* [comment removed for export] *)
          LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMLA.W_parA IC P E ++ W_encA V S2 /\                (* [comment removed for export] *)
          PMLA.pcredit_xA L cr' ps' (kx + kenc eg') (bx + benc eg') /\ Rel ps ps' code R').
Definition ptrans_gbxeA (WFin : pstate -> Prop) (BBin : pstate -> Z -> Prop) (PAin : mem -> Z -> pstate -> Prop) (PAout : pstate -> mem -> Z -> pstate -> Prop)
           (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> Prop)
           (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : pstate) (eg : PMES.eghost),
    cps_asan pc r sp scr (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) FF LK cr A d                                        (* [comment removed for export] *)
      (fun R M => Args R M LBo P V E ps eg /\ (uar = true -> sp mod 32 = 0) /\ stksh M sp scr /\
                  PAin M P ps /\ parser_sh M ps /\ WFin ps /\ win_okA M LBo ps /\ BBin ps B /\ vis_at M V /\ ec_at M E 0 /\ ls_ok g M /\ g <> PML.LS0 /\
                  enc_invA M V S2 eg /\ lits_ok M /\ enc_sync ps eg /\                                                                (* [comment removed for export] *)
                  0 <= kx /\ 0 <= bx /\ PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) /\                                      (* [comment removed for export] *)
                  fobj M FF P 272 /\ fobj M FF V PMES.ENC_SIZE /\ fobj M FF E 16 /\ fobj M FF S2 24 /\                         (* [comment removed for export] *)
                  PMLA.apart P 272 V PMES.ENC_SIZE /\ PMLA.apart P 272 E 16 /\ PMLA.apart V PMES.ENC_SIZE E 16 /\
                  PMLA.apart P 272 S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24 /\ PMLA.apart S2 24 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
          PAout ps M' P ps' /\ parser_sh M' ps' /\ PML.wf_ps ps' /\ win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          enc_invA M' V S2 eg' /\ lits_ok M' /\ (code = 0 -> enc_sync ps' eg') /\                                             (* [comment removed for export] *)
          LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = W_parE P E ++ W_encA V S2 /\                (* [comment removed for export] *)
          PMLA.pcredit_xA L cr' ps' (kx + kenc eg') (bx + benc eg') /\ Rel ps ps' code R').
Definition ptrans_gxA := ptrans_gbxA PML.wf_ps PML.buf_bound.
Definition ptransxA := ptrans_gxA parser_at (fun _ => parser_at).
Definition ptrans_curxA := ptrans_gxA parser_at (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps))).
Definition ptrans_stalexA (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxA PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
               (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.
Definition ptrans_gxeA := ptrans_gbxeA PML.wf_ps PML.buf_bound.
Definition ptransxeA := ptrans_gxeA parser_at (fun _ => parser_at).
Definition ptrans_curxeA := ptrans_gxeA parser_at (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' (PML.ps_win ps))).
Definition ptrans_stalexeA (pc scr d : Z) (uar : bool) (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> pstate -> PMES.eghost -> Prop) (Rel : pstate -> pstate -> Z -> bvmap 5 word -> Prop) : Prop :=
  forall mw : option (Z * Z),
    ptrans_gbxeA PML.wf_ps_stale buf_bound_stale (fun M P ps => parser_at M P (PML.ps_set_win ps mw))
                (fun ps M' P ps' => parser_at M' P (PML.ps_set_win ps' mw) /\ PML.ps_win ps' = PML.ps_win ps) pc scr d uar Args Rel.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition begin_container_specXA (pc kind st' : Z) : Prop :=
  ptransxA pc PFXA_SCR DBEGXA true (fun R M LBo P V E ps eg => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING /\
                                    eroomA eg (PMES.EvBegin (Z.eqb kind PML.ST_ARRAY)))      (* [comment removed for export] *)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_level ps' = PML.ps_level ps + 1 /\ PML.ps_st ps' = st' /\ PML.ps_more ps' = true /\ PML.ps_stack ps' = PML.ps_stack ps ++ [kind] /\ PML.ps_win ps' = PML.ps_win ps)
            \/ (code = 5 /\ PML.ps_level ps = 1024 /\ PML.ps_win ps' = PML.ps_win ps)).
Definition begin_object_specXA (pc : Z) := begin_container_specXA pc PML.ST_OBJECT PML.ST_EXPECT_MEMBER_NAME_OR_END.
Definition begin_array_specXA (pc : Z) := begin_container_specXA pc PML.ST_ARRAY PML.ST_EXPECT_VALUE_OR_END.
Definition end_container_specXA (pc kind : Z) : Prop :=
  ptransxA pc PFXA_SCR DVXA3 true (fun R M LBo P V E ps eg => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ PML.comment_or_cr (PML.ps_st ps) /\ PML.ps_st ps <> PML.ST_STRING /\ eroomA eg PMES.EvEnd)      (* [comment removed for export] *)
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_level ps' = PML.ps_level ps - 1 /\ PML.ps_more ps' = true /\ (exists rest, PML.ps_stack ps = rest ++ [kind] /\ PML.ps_stack ps' = rest) /\
             PML.ps_st ps' = (if Z.eqb (PML.ps_level ps') 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\ PML.ps_win ps' = PML.ps_win ps)
            \/ (In code [20; 21; 22; 23] /\ PML.ps_win ps' = PML.ps_win ps)).
Definition end_object_specXA (pc : Z) := end_container_specXA pc PML.ST_OBJECT.
Definition end_array_specXA (pc : Z) := end_container_specXA pc PML.ST_ARRAY.
Definition parse_true_specXA (pc : Z) : Prop :=
  ptrans_curxA pc PFXA_SCR DVXA2 true (fun R M LBo P V E ps eg => cur_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps) /\ eroomA eg (PMES.EvBool true))      (* [comment removed for export] *)
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_false_specXA (pc : Z) : Prop :=
  ptrans_curxA pc PFXA_SCR DVXA2 true (fun R M LBo P V E ps eg => cur_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps) /\ eroomA eg (PMES.EvBool false))      (* [comment removed for export] *)
         (fun ps ps' code R' => literal_rel ps ps' code /\ not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p)).
Definition parse_null_specXA (pc : Z) : Prop :=
  ptransxA pc PFXA_SCR DVXA2 true (fun R M LBo P V E ps eg => std_args R M P V E ps /\ PML.ps_more ps = true /\ ~ win_exhausted ps /\ PML.is_expect (PML.ps_st ps) /\ eroomA eg PMES.EvNull)      (* [comment removed for export] *)
         (fun ps ps' code R' => literal_rel ps ps' code).
Definition end_string_value_specXA (pc : Z) : Prop :=
  ptrans_stalexA pc ESVXA_SCR DVXA3 true
         (fun R M LBo P V E ps eg => a0 R P /\ a3 R V /\ a4 R E /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING /\ key_ok ps /\      (* [comment removed for export] *)
                              exists s len, a1 R s /\ a2 R len /\ 0 <= len < 2 ^ 26 /\ L5.defined M s len /\
                                            (* [comment removed for export] *)
                                            text_inA M (PML.ps_blocks ps ++ LBo) s len /\
                                            (* [comment removed for export] *)
                                            (forall tag bs, L5.bytes_at (hl_segs L) M s bs -> PMES.len bs = len -> 0 <= tag < 256 -> eroomA eg (PMES.EvKey bs) /\ eroomA eg (PMES.EvStr tag bs)))
         (fun ps ps' code R' =>
            (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps /\
             In (PML.ps_st ps') [PML.ST_EXPECT_COLON; PML.ST_EXPECT_COMMA_OR_END; PML.ST_ACCEPT])
            \/ In code [25; 26; 27; 28; 29]).
Definition parse_string_specXA (pc : Z) : Prop :=
  ptrans_curxA pc PFXA_SCR DPSXA true (fun R M LBo P V E ps eg => cur_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_STRING /\ key_ok ps /\      (* [comment removed for export] *)
                                       (* [comment removed for export] *)
                                       (forall tag bs, PMES.len bs <= Z.of_nat (length (PML.ps_buf ps)) + PML.winlen ps + PML.buf_need ps -> 0 <= tag < 256 -> eroomA eg (PMES.EvKey bs) /\ eroomA eg (PMES.EvStr tag bs)))
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code <> 0 \/ consumed ps ps' \/ win_exhausted ps) /\
                                (code = 0 -> PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps)).
Definition end_number_specXA (pc : Z) : Prop :=
  ptrans_stalexA pc ENDNUMXA_SCR DVXA4 true (fun R M LBo P V E ps eg => std_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps) /\
                                             (* [comment removed for export] *)
                                             eroomA eg PMES.EvI64 /\ eroomA eg PMES.EvU64 /\ eroomA eg (PMES.EvStr 2 (PML.ps_buf ps)))
         (fun ps ps' code R' => (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                 PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) \/ code = 19).
Definition end_integer_value_specXA (pc : Z) := end_number_specXA pc.
Definition end_fraction_value_specXA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptrans_stalexeA pc ENDNUMXA_SCR DVXA4 true (fun R M LBo P V E ps eg => std_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\ PML.num_final (PML.ps_buf ps) /\
                                              (* [comment removed for export] *)
                                              eroomA eg PMES.EvDbl /\ eroomA eg (PMES.EvStr 3 (PML.ps_buf ps)))
         (fun ps ps' code R' => (code = 0 /\ PML.ps_more ps' = true /\ PML.ps_st ps' = (if Z.eqb (PML.ps_level ps) 0 then PML.ST_ACCEPT else PML.ST_EXPECT_COMMA_OR_END) /\
                                 PML.ps_stack ps' = PML.ps_stack ps /\ PML.ps_level ps' = PML.ps_level ps /\ PML.ps_win ps' = PML.ps_win ps) \/ code = 19).
Definition parse_number_specXA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptrans_curxeA pc PFXA_SCR DPNXA true (fun R M LBo P V E ps eg => cur_args R M P V E ps /\ PML.ps_more ps = true /\ PML.ps_st ps = PML.ST_NUMBER /\
                                         (* [comment removed for export] *)
                                         eroomA eg PMES.EvI64 /\ eroomA eg PMES.EvU64 /\ eroomA eg PMES.EvDbl /\
                                         (forall bs, PMES.len bs <= Z.of_nat (length (PML.ps_buf ps)) + PML.winlen ps -> eroomA eg (PMES.EvStr 2 bs) /\ eroomA eg (PMES.EvStr 3 bs)))
         (fun ps ps' code R' => not_retreated ps ps' /\ (exists p e, PML.ps_win ps' = Some (p, e) /\ a0 R' p) /\
                                (code = 0 -> PML.ps_level ps' = PML.ps_level ps /\ PML.ps_more ps' = true /\ (PML.ps_st ps' = PML.ST_NUMBER -> win_exhausted ps') /\
                                             In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END])).
Definition parse_some_specXA (pc : Z) : Prop :=          (* [comment removed for export] *)
  ptransxeA pc PSOMEXA_SCR DPSOMEXA true (fun R M LBo P V E ps eg => std_args R M P V E ps /\ PML.ps_more ps = true (* [comment removed for export] *))
         (fun ps ps' code R' =>
            (code <> 0 \/ PML.ps_more ps' = false \/ win_exhausted ps') /\
            (PML.ps_st ps = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
            (win_exhausted ps -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR]) /\
            (code = 0 -> PML.ws_ok ps')).


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition skip_space_spec2A (pc : Z) : Prop :=
  PMSA.ptransA L ar HI IC pc PF_SCR 4 false
    (fun R M (LBo : list (Z * Z)) P V E ps => a0 R P /\ a1 R (P + 200) /\ PML.ws_ok ps /\ (if PML.ps_more ps then PML.is_expect (PML.ps_st ps) else PML.ps_st ps = PML.ST_DONE) /\
                             exists p e b, PML.ps_win ps = Some (p, e) /\ p < e /\ u8 M p b /\ In b [9; 10; 13; 32])
    (fun ps ps' code R' => code = 0 /\ consumed ps ps' /\ PML.ps_more ps' = PML.ps_more ps /\ PML.ws_ok ps' /\
                            ((PML.ps_st ps' = PML.ps_st ps /\ PML.ps_stack ps' = PML.ps_stack ps) \/
                             (PML.ps_st ps' = PML.ST_CR /\ win_exhausted ps' /\ PML.ps_stack ps' = PML.ps_stack ps ++ [PML.ps_st ps])) /\
                            PML.ps_level ps' = PML.ps_level ps).
(* [comment removed for export] *)
Lemma skip_space_spec2A_weaken : forall pc, skip_space_spec2A pc -> PMSA.skip_space_specA L ar HI IC pc.
Proof.
  intros pc H LBo FF LK cr A sp r P V E B kx bx g ps fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  apply (H LBo FF LK cr A sp r P V E B kx bx g ps fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE).
  intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (ps' & code & g' & X) HRP HP Hrt HA Hmo' HLK HH'.
  apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|exact HRP | exact HP | exact Hrt | exact HA | exact Hmo' | exact HLK | exact HH'].
  exists ps', code, g'. destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & (R1 & R2 & R3 & R4 & R5 & R6)).
  repeat (split; [assumption|]). split; [|exact R6].
  destruct R5 as [(Q & _)|(Q1 & Q2 & _)]; [left; exact Q | right; split; [exact Q1 | exact Q2]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W_parxA_app : forall P V E S2, W_parxA P V E S2 = PMLA.W_parA IC P E ++ W_encA V S2.
Proof. intros; reflexivity. Qed.
End SpecsXA.
End PMXA.
