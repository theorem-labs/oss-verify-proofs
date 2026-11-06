(* fuzz_recv on image A: the trailing-header loop +0x110 .. +0x1c8 of its walk, the piece RV_LOOP of
   lib/A/Prog/fuzz_recv_defs.v (listing (internal path)
   (internal record, sha256 549eae89aefb)). One turn from the loop head with s4 = t:
   - rl_head, +0x110 .. +0x120: s9 := buf + t; the call of checked_memset(s9 - 30, 0, 30) (fuzz_recv_kit2.v
     rv_intrin): the bytes [buf + t - 30, buf + t) become 0, every other byte outside the callee's window is kept;
   - rl_body, +0x124 .. +0x1c8: the six instrumented checks of the record's three byte groups [s9 - 36, s9 - 32),
     [s9 - 32, s9 - 30), [s9 - 20, s9 - 16) (the shadow entry rv_body_SH, from the buffer's addressable range,
     covers them all: no obligation, no error path), the ten byte stores into these groups (buffer bytes, so bytes
     of the write set), s4 += 36, `bgeu s0, s4`: back to the loop head with s4 = t + 36, or +0x1cc `j +0x23c` to the
     epilogue (RV_RET, with the Post RV_CPOST);
   - across the turn the chunk [buf, buf + clen) is untouched (every write is at or above buf + t - 36, and
     t - 36 >= the rounded chunk length), every buffer byte stays defined, g_nl's next and misuse are kept.
   rv_loop_ok: induction on the bytes left, len - t.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkErrno fuzz_recv_c fuzz_recv_defs fuzz_recv_kit fuzz_recv_kit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation VAL := (@pa_val _ link_listing PI).
#[local] Abbreviation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis MEMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
Variable c : rvc.
Hypothesis HC : rv_call SK B c.

(* ---- the bounds the turn needs ---- *)
Lemma rl_bnd : 0 < rv_buf c /\ NL_CHUNK_MAX <= rv_len c /\ rv_buf c + rv_len c < 2 ^ 47 /\
  (rv_buf c + rv_len c <= rv_sp c - 96 - ESTACK \/ rv_sp c <= rv_buf c) /\
  (rv_buf c + rv_len c <= LA_G_NL \/ LA_G_NL + NK_SIZE <= rv_buf c) /\
  (rv_buf c + rv_len c <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= rv_buf c) /\
  LA_G_NL + NK_SIZE < rv_sp c - 96 - ESTACK /\ 96 <= rv_sp c <= 2 ^ 47.
Proof.
  destruct (rv_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & _ & HXO).
  destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & _).
  pose proof asan_consts as ((C1a & _) & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
  unfold apart_gnl, apart_frame in *. unfold rv_sp in *.
  unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL, NK_SIZE, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* the chunk arm's chunk length: at most 4096, at most its rounding up to 4 *)
Lemma rl_clen : nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
  0 <= rv_clen c <= NL_CHUNK_MAX /\ rv_clen c <= rv_o c /\ 0 <= rv_o c.
Proof.
  intros Hnx. pose proof HC as (_ & _ & WF & _).
  pose proof WF as (_ & Wnx & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wcl & _).
  assert (Hcl : 0 <= rv_clen c <= NL_CHUNK_MAX) by (unfold rv_clen; apply Wcl; lia).
  unfold rv_o. pose proof (Z.div_mod (rv_clen c + 3) 4 ltac:(lia)).
  pose proof (Z.mod_pos_bound (rv_clen c + 3) 4 ltac:(lia)).
  unfold NL_CHUNK_MAX in *. lia.
Qed.

(* ---- small facts ---- *)
Lemma rl_agree : forall regs, env_agree 32 (Ereg regs (rv_ext c)) (rv_E c regs).
Proof. intros regs. split; [intros n Hn; unfold rv_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma rl_add : forall E x k y v1 v2, ew E x = Z_to_bv 64 v1 -> ew E y = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 + k + v2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff x k) (SOff y 0)) = Z_to_bv 64 (v1 + k + v2).
Proof.
  intros E x k y v1 v2 H1 H2 R1 R2 R3. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H1, H2, !unsigned_lit_small by lia.
  rewrite Z.add_0_r. unfold zcanon, M64.
  rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia. apply Z.mod_small. lia.
Qed.

(* a defined byte stays defined when the memory grows *)
Lemma rl_def_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview SEGS H m a <> None -> aview SEGS H m' a <> None.
Proof.
  intros H m m' a HG Hd. unfold aview, mbyte in *.
  destruct (mrestrict H m' (Z_to_bv 64 a)) eqn:E2; [cbn; discriminate|].
  destruct (mrestrict H m (Z_to_bv 64 a)) eqn:E1; [|exact Hd].
  exfalso. exact (HG (Z_to_bv 64 a) ltac:(rewrite E1; discriminate) E2).
Qed.

(* a buffer byte is writable at every memory of the walk *)
Lemma rl_wr : forall regs mem md, rv_inv SK B c regs mem md ->
  forall a, rv_buf c <= a < rv_buf c + rv_len c -> writable_at SEGS (rdW (c_W c) mem) a.
Proof.
  intros regs mem md HI a Ha. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Habuf & _).
  apply (writable_kept (w_H (c_W c)) (c_memc c) mem a (PR a)).
  destruct Habuf as (junk & Hjl & _ & Hwr). unfold awrange in Hwr.
  replace a with (aarg (c_regs0 c) 1 + (a - aarg (c_regs0 c) 1)) by ring.
  apply Hwr. rewrite Hjl. unfold rv_buf, rv_len in Ha. lia.
Qed.

(* a run whose write windows are buffer bytes writes only bytes of the write set (apre's ajw) *)
Lemma rl_awr_buf : forall E (rs : smem),
  (forall r, In r rs -> forall a,
     base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     rv_buf c <= a < rv_buf c + rv_len c) ->
  awr_ok_xe B E rs (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
    (ablocks B (c_lyc c) (c_Sc c)) (c_lyc c) (c_own c).
Proof.
  intros E rs Hrs a (r & Hin & Ha).
  pose proof HC as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  left. apply Hajw. exists (aarg (c_regs0 c) 1, aarg (c_regs0 c) 1 + aarg (c_regs0 c) 2).
  split; [unfold fuzz_recv_awr; cbn [In]; right; left; reflexivity | exact (Hrs r Hin a Ha)].
Qed.

(* rv_cmem after a step that writes [lo, hi) inside the buffer above the padded chunk, leaves its bytes defined,
   and keeps every other byte outside the callees' window *)
Lemma rl_cmem_step : forall mem mem' lo hi,
  rv_cmem c mem -> nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
  rv_buf c + rv_o c <= lo -> hi <= rv_buf c + rv_len c ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (rv_sp c - 96 - ESTACK <= a < rv_sp c - 96) ->
     aview SEGS (w_H (c_W c)) mem' a = aview SEGS (w_H (c_W c)) mem a) ->
  (forall a, lo <= a < hi -> aview SEGS (w_H (c_W c)) mem' a <> None) ->
  rv_cmem c mem'.
Proof.
  intros mem mem' lo hi (C1 & C2 & C3 & C4) Hnx Hlo Hhi UN DEF.
  destruct rl_bnd as (Hb0 & Hlen & Hbhi & Hbf & Hbg & _ & Hgs & Hsp).
  destruct (rl_clen Hnx) as (Hc0 & Hco & Ho0).
  assert (K : forall a, rv_buf c <= a < rv_buf c + rv_len c -> ~ (lo <= a < hi) ->
            aview SEGS (w_H (c_W c)) mem' a = aview SEGS (w_H (c_W c)) mem a).
  { intros a Ha Hn. apply UN; [clear - Ha Hb0 Hbhi; lia | exact Hn | clear - Ha Hbf; lia]. }
  assert (Kg : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
             aview SEGS (w_H (c_W c)) mem' a = aview SEGS (w_H (c_W c)) mem a).
  { intros a Ha. apply UN.
    - clear - Ha. unfold LA_G_NL, NK_SIZE in *. lia.
    - clear - Ha Hlo Hhi Hbg Ho0 Hb0. lia.
    - clear - Ha Hgs. lia. }
  split; [|split; [|split]].
  - intros i Hi. rewrite (K (rv_buf c + i)); [exact (C1 i Hi) | clear - Hi Hc0 Hco Hlen; lia | clear - Hi Hco Hlo; lia].
  - intros i Hi. destruct (Z_lt_le_dec (rv_buf c + i) lo) as [Hl|Hl].
    + rewrite (K (rv_buf c + i)); [exact (C2 i Hi) | clear - Hi; lia | clear - Hl; lia].
    + destruct (Z_lt_le_dec (rv_buf c + i) hi) as [Hh|Hh]; [exact (DEF _ (conj Hl Hh))|].
      rewrite (K (rv_buf c + i)); [exact (C2 i Hi) | clear - Hi; lia | clear - Hh; lia].
  - refine (val_mem_kept (w_H (c_W c)) mem mem' _ _ _ _ C3). intros k Hk. cbn in Hk.
    apply Kg. clear - Hk. unfold NK_NEXT, NK_SIZE. lia.
  - refine (val_mem_kept (w_H (c_W c)) mem mem' _ _ _ _ C4). intros k Hk. cbn in Hk.
    apply Kg. clear - Hk. unfold NK_MISUSE, NK_SIZE. lia.
Qed.

(* the invariant and rv_cmem after the record's runs (+0x124 .. the next stop): they write the record's byte groups
   [buf + t - 36, buf + t) only and grow the memory *)
Lemma rl_post_body : forall t regs mem md regs3 mem3 md3,
  rv_inv SK B c regs mem md -> rv_cmem c mem -> nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
  rv_o c + 36 <= t <= rv_len c ->
  ajournal_gx SEGS B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c)
    (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) (c_W c) mem3 md3 (c_k c) ->
  m_fds md3 = m_fds md -> m_fs md3 = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rv_buf c + t - 36 <= a < rv_buf c + t) ->
     aview SEGS (w_H (c_W c)) mem3 a = aview SEGS (w_H (c_W c)) mem a) ->
  mem_grows (rdW (c_W c) mem) (rdW (c_W c) mem3) ->
  getr regs3 2 = getr regs 2 -> getr regs3 3 = getr regs 3 -> getr regs3 4 = getr regs 4 ->
  getr regs3 26 = getr regs 26 -> getr regs3 27 = getr regs 27 ->
  rv_inv SK B c regs3 mem3 md3 /\ rv_cmem c mem3.
Proof.
  intros t regs mem md regs3 mem3 md3 HI HCM Hnx Ht HJ3 Hfd Hfs UN HG E2 E3 E4 E26 E27.
  destruct rl_bnd as (Hb0 & Hlen & Hbhi & _ & _ & _ & _ & _).
  destruct (rl_clen Hnx) as (_ & _ & Ho0).
  split.
  - apply (rv_inv_step SK B TL c HC regs mem md regs3 mem3 md3 (fun a => rv_buf c + t - 36 <= a < rv_buf c + t)
      HI HJ3 Hfd Hfs UN); [| intros a Hp; exact (apresent_grows _ _ _ _ HG Hp)
      | exact E2 | exact E3 | exact E4 | exact E26 | exact E27].
    intros a Ha. right. unfold rv_ewr. right; right; left. cbv beta in Ha. clear - Ha Ht Ho0. lia.
  - apply (rl_cmem_step mem mem3 (rv_buf c + t - 36) (rv_buf c + t) HCM Hnx);
      [clear - Ht; lia | clear - Ht; lia | |].
    + intros a Ha Hn _. exact (UN a Ha Hn).
    + intros a Ha. apply (rl_def_grows (w_H (c_W c)) mem mem3 a HG).
      pose proof HCM as (_ & C2 & _). replace a with (rv_buf c + (a - rv_buf c)) by ring.
      apply C2. clear - Ha Ht Ho0. lia.
Qed.

(* ---- the fresh state after the loop's checked_memset (+0x124) and its shadow entry ---- *)
Lemma rl_body_st : forall t regs mem md,
  rv_inv SK B c regs mem md -> getr regs 19 = w64 SHADOW_OFF -> getr regs 25 = w64 (rv_buf c + t) ->
  36 <= t <= rv_len c ->
  st_ok_pi SEGS VAL (rv_E c regs) ss_bd
    (restrict (w_H (c_W c)) (mkst regs (Z_to_bv 64 (BASE + RV_BD)) mem (seg_rom SEGS))).
Proof.
  intros t regs mem md HI H19 H25 Ht.
  destruct rl_bnd as (Hb0 & _ & Hbhi & Hbf & _ & _ & Hgs & Hsp).
  unfold ESTACK in Hbf, Hgs.
  pose proof HI as (_ & _ & _ & Hsp2 & _).
  assert (U25 : bv_unsigned (ew (rv_E c regs) 25) = rv_buf c + t).
  { rewrite (rv_E_reg c regs 25 25%bv) by (lia || reflexivity). rewrite H25. apply unsigned_lit_small. lia. }
  assert (U2 : bv_unsigned (ew (rv_E c regs) 2) = rv_sp c - 96).
  { rewrite (rv_E_reg c regs 2 2%bv) by (lia || reflexivity). rewrite Hsp2. apply unsigned_lit_small.
    unfold LA_G_NL, NK_SIZE in Hgs. lia. }
  unfold ss_bd. apply (rv_st_ok SK B c HC regs mem md RV_BD rv_body_rs _ HI H19).
  - vm_compute. reflexivity.
  - unfold rv_body_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U25;
      (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply (rl_wr regs mem md HI); lia | constructor]).
  - apply all_disjoint_of_extents. unfold rv_fr, rv_body_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U25.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - apply pairwise_disjoint_of_extents. unfold rv_body_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25, Z.pow_0_r, Z.mod_1_r.
    repeat split; lia.
Qed.

Lemma rl_body_sh : forall t regs mem md,
  rv_inv SK B c regs mem md -> getr regs 19 = w64 SHADOW_OFF -> getr regs 25 = w64 (rv_buf c + t) ->
  36 <= t <= rv_len c ->
  sh_ok SEGS rv_Bx rv_body_SH (rv_E c regs) (mrestrict (w_H (c_W c)) mem).
Proof.
  intros t regs mem md HI H19 H25 Ht.
  destruct rl_bnd as (Hb0 & Hlen & Hbhi & _ & _ & Hbs & _ & _).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrab & _).
  assert (E19 : ew (rv_E c regs) 19 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (rv_E_reg c regs 19 19%bv) by (lia || reflexivity); exact H19).
  assert (E25 : ew (rv_E c regs) 25 = Z_to_bv 64 (rv_buf c + t))
    by (rewrite (rv_E_reg c regs 25 25%bv) by (lia || reflexivity); exact H25).
  unfold rv_body_SH. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold rv_Bx.
  rewrite (U_atom _ 19 SHADOW_OFF E19) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 25 (rv_buf c + t) E25) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS).
    apply (range_addressable_sub _ _ (rv_buf c) (rv_len c)); [| lia | lia].
    apply (rv_ra_kept SK B TL c HC regs mem md (rv_buf c) (rv_len c) HI); [lia | unfold kHighMemEnd; lia | exact Hrab].
  - intros a Ha. rewrite (Z.min_l (-36) 0), (Z.max_r (-36) 0) in Ha by lia.
    clear - Ha Hbs Ht. lia.
Qed.

(* ---- tactics of the turn ---- *)
Ltac rl_inl := repeat (first [left; reflexivity | right]).
Ltac rl_keep RK r K := pose proof (RK r ltac:(rl_inl)) as K; cbn [ms_regs restrict] in K.
(* a register's symbolic value at a stop, unnormalised *)
Ltac rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
(* the write permission of a run whose only region is the frame (no write window) *)
Ltac rl_awr0 :=
  apply rl_awr_buf; intros ?r ?Hin ?a ?Ha; vm_compute in Hin;
  destruct Hin as [?Hq | []]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; exfalso; clear - Ha; lia.
(* the write permission of a run over the frame and the record's three byte groups at atom 25 = buf + t *)
Ltac rl_awr U25 Ht :=
  apply rl_awr_buf; intros ?r ?Hin ?a ?Ha; vm_compute in Hin;
  repeat (destruct Hin as [?Hq | Hin];
    [ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ exfalso; clear - Ha; lia | rewrite U25 in Ha; clear - Ha Ht; lia ] | ]);
  destruct Hin.
(* each write window of such a run lies in [buf + t - 36, buf + t) *)
Ltac rl_win U25 :=
  intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
  repeat (destruct Hin as [?Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta;
      first [ exfalso; clear - Hrr; lia | rewrite U25 in Hrr; clear - Hrr; lia ] | ]);
  destruct Hin.

(* ---- +0x124 .. +0x1c8: the record, s4 += 36, `bgeu s0, s4` ---- *)
Lemma rl_body : forall t regs mem md,
  rv_inv SK B c regs mem md -> rv_cmem c mem -> nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
  rv_o c + 36 <= t <= rv_len c -> rv_cregs c regs -> getr regs 20 = w64 t -> getr regs 25 = w64 (rv_buf c + t) ->
  RV_RET SK B c -> RV_CPOST SK B c ->
  (t + 36 <= rv_len c -> forall regs2 mem2 md2, rv_inv SK B c regs2 mem2 md2 -> rv_cmem c mem2 ->
     rv_cregs c regs2 -> getr regs2 20 = w64 (t + 36) -> rv_goal SK B c (cfg_of regs2 (BASE + RV_LP) mem2 md2)) ->
  rv_goal SK B c (cfg_of regs (BASE + RV_BD) mem md).
Proof.
  intros t regs mem md HI HCM Hnx Ht HCR H20 H25 HRET HCP IH.
  unfold RV_RET, RV_CPOST, rv_goal in *.
  pose proof HCR as (H8 & H9 & H18 & H19).
  destruct rl_bnd as (Hb0 & Hlen & Hbhi & _ & _ & _ & _ & _).
  destruct (rl_clen Hnx) as (_ & _ & Ho0).
  assert (Ht36 : 36 <= t <= rv_len c) by (clear - Ht Ho0; lia).
  assert (Hl64 : 0 <= rv_len c < 2 ^ 64) by (clear - Hb0 Hbhi Hlen; unfold NL_CHUNK_MAX in Hlen; lia).
  assert (Ht64 : 0 <= t + 36 < 2 ^ 64) by (clear - Hb0 Hbhi Ht36; lia).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  assert (E8 : ew (rv_E c regs) 8 = Z_to_bv 64 (rv_len c))
    by (rewrite (rv_E_reg c regs 8 8%bv) by (lia || reflexivity); exact H8).
  assert (E20 : ew (rv_E c regs) 20 = Z_to_bv 64 t)
    by (rewrite (rv_E_reg c regs 20 20%bv) by (lia || reflexivity); exact H20).
  assert (U25 : bv_unsigned (ew (rv_E c regs) 25) = rv_buf c + t).
  { rewrite (rv_E_reg c regs 25 25%bv) by (lia || reflexivity). rewrite H25. apply unsigned_lit_small.
    clear - Hb0 Hbhi Ht36; lia. }
  pose proof (rl_body_st t regs mem md HI H19 H25 Ht36) as HS.
  pose proof (rl_body_sh t regs mem md HI H19 H25 Ht36) as SHOK.
  pose proof (rv_E_env c regs) as HEI.
  pose proof (rl_agree regs) as HAE.
  pose proof (paj_run_xe SK B LAWS (pal_env B TL) ERRF (c_G c) HGX (c_XO c) (c_OUT c)) as RUN.
  pose proof (paj_run_to_xe SK B LAWS (pal_env B TL) ERRF (c_G c) HGX (c_XO c) (c_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  (* +0x124 .. +0x1c4: the six instrumented checks, the ten byte stores, s4 += 36; the run stops at `bgeu s0, s4` *)
  paj_run_tok RUN HS HJ SHOK rv_span; [rl_awr U25 Ht36 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => rv_buf c + t - 36 <= a < rv_buf c + t) HFr
    ltac:(rl_win U25)) as UN2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK rv_span;
    rewrite branch_geu_U, (U_atom _ 8 (rv_len c) E8), (U_atom_off _ 20 t 36 E20) in Hc
      by (clear - Hl64 Ht64 Ht36 Hb0; lia).
  - (* t + 36 <= len: back to the loop head +0x110 with s4 = t + 36 *)
    apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rv_span RV_LP; [rl_awr U25 Ht36 |].
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => rv_buf c + t - 36 <= a < rv_buf c + t) HFr
      ltac:(rl_win U25)) as UN3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
    pmkst HS.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rv_ext c)
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 26%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
    rl_keep RK (2%bv : bv 5) K2. rl_keep RK (3%bv : bv 5) K3. rl_keep RK (4%bv : bv 5) K4.
    rl_keep RK (8%bv : bv 5) K8. rl_keep RK (9%bv : bv 5) K9. rl_keep RK (18%bv : bv 5) K18.
    rl_keep RK (19%bv : bv 5) K19. rl_keep RK (26%bv : bv 5) K26. rl_keep RK (27%bv : bv 5) K27.
    rreg HS (20%bv : bv 5) R20.
    rewrite denot_lit_U, (U_atom_off _ 20 t 36 E20) in R20 by (clear - Ht64 Ht36; lia).
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ =>
      destruct (rl_post_body t regs mem md (ms_regs ms3) (ms_mem ms3) m HI HCM Hnx Ht HJ
        ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
        ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
        (fun a Ha Hz => eq_trans (UN3 a Ha Hz) (UN2 a Ha Hz)) (mem_grows_trans _ _ _ HG2 HG)
        K2 K3 K4 K26 K27) as (HI3 & HCM3) end.
    refine (IH Hc (ms_regs ms3) (ms_mem ms3) _ HI3 HCM3 _ R20).
    refine (conj _ (conj _ (conj _ _))).
    + rewrite K8. exact H8.
    + rewrite K9. exact H9.
    + rewrite K18. exact H18.
    + rewrite K19. exact H19.
  - (* len < t + 36: +0x1cc `j +0x23c`, the epilogue *)
    apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK rv_span RV_RT; [rl_awr U25 Ht36 |].
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => rv_buf c + t - 36 <= a < rv_buf c + t) HFr
      ltac:(rl_win U25)) as UN3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
    pmkst HS.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rv_ext c)
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 26%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
    rl_keep RK (2%bv : bv 5) K2. rl_keep RK (3%bv : bv 5) K3. rl_keep RK (4%bv : bv 5) K4.
    rl_keep RK (18%bv : bv 5) K18. rl_keep RK (19%bv : bv 5) K19. rl_keep RK (26%bv : bv 5) K26.
    rl_keep RK (27%bv : bv 5) K27.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ =>
      destruct (rl_post_body t regs mem md (ms_regs ms3) (ms_mem ms3) m HI HCM Hnx Ht HJ
        ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
        ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
        (fun a Ha Hz => eq_trans (UN3 a Ha Hz) (UN2 a Ha Hz)) (mem_grows_trans _ _ _ HG2 HG)
        K2 K3 K4 K26 K27) as (HI3 & HCM3) end.
    apply (HRET (ms_regs ms3) (ms_mem ms3) _ HI3); [rewrite K19; exact H19 |].
    intros regs2 H10. apply (HCP (ms_regs ms3) (ms_mem ms3) _ regs2 HI3 HCM3 Hnx).
    rewrite H10, K18. exact H18.
Qed.

(* ---- +0x110 .. +0x120: s9 := buf + t, checked_memset(s9 - 30, 0, 30) ---- *)
Lemma rl_head : forall t regs mem md,
  rv_inv SK B c regs mem md -> rv_cmem c mem -> nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
  rv_o c + 36 <= t <= rv_len c -> rv_cregs c regs -> getr regs 20 = w64 t ->
  (forall regs2 mem2 md2, rv_inv SK B c regs2 mem2 md2 -> rv_cmem c mem2 -> rv_cregs c regs2 ->
     getr regs2 20 = w64 t -> getr regs2 25 = w64 (rv_buf c + t) ->
     rv_goal SK B c (cfg_of regs2 (BASE + RV_BD) mem2 md2)) ->
  rv_goal SK B c (cfg_of regs (BASE + RV_LP) mem md).
Proof.
  intros t regs mem md HI HCM Hnx Ht HCR H20 K.
  unfold rv_goal in *.
  pose proof HCR as (H8 & H9 & H18 & H19).
  destruct rl_bnd as (Hb0 & Hlen & Hbhi & _ & _ & _ & _ & _).
  destruct (rl_clen Hnx) as (_ & Hco & Ho0).
  assert (Ht36 : 36 <= t <= rv_len c) by (clear - Ht Ho0; lia).
  assert (HBD : 0 <= RV_BD < 2 ^ 40) by (unfold RV_BD, AF_fuzz_recv; lia).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  assert (E9 : ew (rv_E c regs) 9 = Z_to_bv 64 (rv_buf c))
    by (rewrite (rv_E_reg c regs 9 9%bv) by (lia || reflexivity); exact H9).
  assert (E20 : ew (rv_E c regs) 20 = Z_to_bv 64 t)
    by (rewrite (rv_E_reg c regs 20 20%bv) by (lia || reflexivity); exact H20).
  pose proof (rv_st_ok SK B c HC regs mem md RV_LP [] [] HI H19 eq_refl (Forall_nil _) I I I) as HS.
  pose proof (rv_E_env c regs) as HEI.
  pose proof (rl_agree regs) as HAE.
  assert (SHOK : sh_ok SEGS rv_Bx [] (rv_E c regs) (mrestrict (w_H (c_W c)) mem)) by constructor.
  pose proof (paj_run_xe SK B LAWS (pal_env B TL) ERRF (c_G c) HGX (c_XO c) (c_OUT c)) as RUN.
  (* +0x110 .. +0x11c: s9 := buf + t, a0 := s9 - 30, a2 := 30, a1 := 0; the run stops at the call +0x120 *)
  paj_run_tok RUN HS HJ SHOK rv_span; [rl_awr0 |].
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms1 end.
  assert (Emem : ms_mem ms1 = mem).
  { apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. clear - Hr. lia. }
  pmkst HS. rewrite Emem in HJ |- *.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs (rv_ext c)
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 26%bv; 27%bv] HS HAE ltac:(vm_compute; reflexivity)) as RK.
  rl_keep RK (2%bv : bv 5) K2. rl_keep RK (3%bv : bv 5) K3. rl_keep RK (4%bv : bv 5) K4.
  rl_keep RK (8%bv : bv 5) K8. rl_keep RK (9%bv : bv 5) K9. rl_keep RK (18%bv : bv 5) K18.
  rl_keep RK (19%bv : bv 5) K19. rl_keep RK (20%bv : bv 5) K20. rl_keep RK (26%bv : bv 5) K26.
  rl_keep RK (27%bv : bv 5) K27.
  rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
  rreg HS (12%bv : bv 5) R12. rreg HS (25%bv : bv 5) R25.
  rewrite (rl_add _ 9 (-30) 20 (rv_buf c) t E9 E20) in R10 by (clear - Hb0 Hbhi Ht36; lia).
  rewrite (rl_add _ 9 0 20 (rv_buf c) t E9 E20) in R25 by (clear - Hb0 Hbhi Ht36; lia).
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ =>
    assert (HI1 : rv_inv SK B c (ms_regs ms1) mem m) end.
  { apply (rv_inv_step SK B TL c HC regs mem md (ms_regs ms1) mem _ (fun _ => False) HI HJ).
    - repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
    - repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
    - intros a _ _; reflexivity.
    - intros a [].
    - intros a Hp; exact Hp.
    - exact K2.
    - exact K3.
    - exact K4.
    - exact K26.
    - exact K27. }
  assert (Ha0 : getr (ms_regs ms1) 10 = w64 (rv_buf c + t - 30)) by (rewrite R10; unfold w64; f_equal; ring).
  assert (Ha1 : getr (ms_regs ms1) 11 = w64 0) by (rewrite R11; reflexivity).
  assert (Ha2 : getr (ms_regs ms1) 12 = w64 30) by (rewrite R12; reflexivity).
  assert (Hra : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + RV_BD)) by (rewrite R1; exact (codeptr_val _ 804 HEI)).
  assert (Hd1 : rv_buf c <= rv_buf c + t - 30) by (clear - Ht36; lia).
  assert (Hd2 : rv_buf c + t - 30 + 30 <= rv_buf c + rv_len c) by (clear - Ht36; lia).
  (* the call +0x120 of checked_memset into the buffer *)
  eapply SRr_bind.
  { exact (rv_intrin SK B LAWS TL c HC OSet _ MEMSET (ms_regs ms1) mem _ (rv_buf c + t - 30) 0 30
      (Z_to_bv 64 (BASE + RV_BD)) HI1 Ha0 Ha1 Ha2 ltac:(clear - Hd1; lia) Hd1 Hd2 Hra
      (ret_ok_codeptr_v RV_BD HBD eq_refl) I). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HI2 & HP2 & Hset & Hkeep).
  cbv iota beta in Hset.
  destruct (rv_preserved (ms_regs ms1) regs2 HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P25 & P26 & P27).
  assert (HCM2 : rv_cmem c mem2).
  { apply (rl_cmem_step mem mem2 (rv_buf c + t - 30) (rv_buf c + t) HCM Hnx);
      [clear - Ht Hco Ho0; lia | clear - Ht36; lia | |].
    - intros a Ha Hn Hw. apply Hkeep; [exact Ha | clear - Hn; lia | exact Hw].
    - intros a Ha. replace a with (rv_buf c + t - 30 + (a - (rv_buf c + t - 30))) by ring.
      rewrite Hset by (clear - Ha; lia). discriminate. }
  apply (K regs2 mem2 md2 HI2 HCM2).
  - refine (conj _ (conj _ (conj _ _))).
    + rewrite P8, K8. exact H8.
    + rewrite P9, K9. exact H9.
    + rewrite P18, K18. exact H18.
    + rewrite P19, K19. exact H19.
  - rewrite P20, K20. exact H20.
  - rewrite P25, R25. unfold w64. f_equal. ring.
Qed.

(* THE PIECE: the loop, by induction on the bytes left *)
Lemma rv_loop_ok : RV_RET SK B c -> RV_CPOST SK B c -> RV_LOOP SK B c.
Proof.
  intros HRET HCP.
  assert (IND : forall n t regs mem md, rv_len c - t < 36 * Z.of_nat n ->
    rv_inv SK B c regs mem md -> rv_cmem c mem -> nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
    rv_o c + 36 <= t <= rv_len c -> rv_cregs c regs -> getr regs 20 = w64 t ->
    rv_goal SK B c (cfg_of regs (BASE + RV_LP) mem md)).
  { induction n as [|n IHn]; intros t regs mem md Hn HI HCM Hnx Ht HCR H20; [exfalso; clear - Hn Ht; lia|].
    apply (rl_head t regs mem md HI HCM Hnx Ht HCR H20).
    intros regs2 mem2 md2 HI2 HCM2 HCR2 H20' H25'.
    apply (rl_body t regs2 mem2 md2 HI2 HCM2 Hnx Ht HCR2 H20' H25' HRET HCP).
    intros Hle regs3 mem3 md3 HI3 HCM3 HCR3 H20''.
    apply (IHn (t + 36) regs3 mem3 md3);
      [clear - Hn; lia | exact HI3 | exact HCM3 | exact Hnx | clear - Ht Hle; lia | exact HCR3 | exact H20'']. }
  unfold RV_LOOP. intros t regs mem md HI HCM Hnx Ht HCR H20.
  apply (IND (Z.to_nat (rv_len c - t + 1)) t regs mem md);
    [clear - Ht; lia | exact HI | exact HCM | exact Hnx | exact Ht | exact HCR | exact H20].
Qed.

End w.

