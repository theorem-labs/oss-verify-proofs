(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S2 of the ASan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput (fuzz_scene.asan, sha256
   43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026): cut C2 0x82ca8 .. cut C3 0x82d74.
   Rule 24: no function proved; `seg_S2 : seg_S2_stmt` (lib/A/P_LLVMFuzzerTestOneInput_seg.v) is a segment lemma.
   The walk: blk's unpoison 0x82cac-0x82cd0, __asan_memset(blk, 0xa5, 34) 0x82ce0 (aj_intrin_at OSet),
   reac_ctrl_build_scene_step(blk, body, n', step) 0x82cfc (a Theorem Labs lane's contract on the caller's journal), the result check
   `bne a0, a1` 0x82d28 whose target is the abort at 0x83144 (__asan_handle_no_return; abort): REFUTED in both arms,
   a0 being build_scene_step's result and a1 = -(n' <> 8904 | sx16(256 b4) < 0 | sx16(step) >= 343) equal to it
   (HA1).  Then on the refusing arm (a0 = -1) the 34-turn loop 0x82d3c-0x82d50 reads blk, still the 0xa5 bytes the
   memset wrote, so a0 folds to 0 and `beqz a0` 0x82d58 reaches C3: the `j` 0x82d5c to the same abort is never
   stepped.  On the accepting arm (a0 = 0) `beqz a0` 0x82d30 goes to check_step(blk, body, step) 0x82d6c (a Theorem Labs lane's
   tcheck_step_specX through cl_callS) and 0x82d70 reloads the flags.  Both arms meet C3 through one lemma, JOIN.
   No __asan_report_* branch lies in 0x82ca8..0x82d74. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC4b YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_reac_ctrl_build_scene_step.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame P_check_step_cut P_check_step.
(* lib/A/S2AluLemmas.v (at a28950bc27b): s2a_snez_xor, s2a_slt_sext16, image-free. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import S2AluLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h: the sink head is a named Section Context, fully qualified, passed by name below *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
(* ---- small image-free helpers; the same four that lib/A/P_check_step_S3.v:92-128 uses, under this
   lane's names (shadow arithmetic, a shadow cell read out of a symbolic region, and what a run keeps). ---- *)
Lemma s2_div8_add : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof.
intros x c Hx. rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hx, Z.add_0_r.
replace (8 * (x / 8) + 8 * c) with ((x / 8 + c) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma s2_ra_part : forall (rd : reader) a q r, a mod 8 = 0 -> 0 <= q -> 0 < r < 8 ->
(forall i, 0 <= i < q -> rd (SHADOW_OFF + a / 8 + i) = Some 0) -> rd (SHADOW_OFF + a / 8 + q) = Some r ->
range_addressable rd SHADOW_OFF a (8 * q + r).
Proof.
intros rd a q r Ha Hq Hr H0 Hl x Hx. unfold shadow_of_addr.
assert (Ex : x / 8 = a / 8 + (x - a) / 8).
{ replace x with (a + (x - a)) at 1 by lia. rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
  replace (8 * (a / 8) + (x - a)) with ((x - a) + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (Hd : 0 <= (x - a) / 8 < q + 1) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Ex, Z.add_assoc.
destruct (Z.eq_dec ((x - a) / 8) q) as [Eq|Nq].
- rewrite Eq. exists r. split; [exact Hl|]. right.
  assert (Hm : x mod 8 = (x - a) mod 8).
  { rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
    replace (x - 8 * (a / 8)) with (x + (- (a / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Hdm. rewrite Eq in Hdm. lia.
- exists 0. split; [apply H0; lia | left; reflexivity].
Qed.
Lemma s2_shb : forall E (H : word -> bool) mem n b cs lo hi wlo whi od v,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
aview SEGS H mem (b + od) = Some v.
Proof.
intros E H mem n b cs lo hi wlo whi od v HR Hn Hc Hv.
apply aview_of_val_mem1; [|exact Hv].
exact (field_of_region E _ n b cs lo hi wlo whi od 1 (SLit v) v HR Hn Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma s2_kept_run : forall E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H mB a = aview SEGS H mA a.
Proof. intros E rs H mA mB a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.

Section h.
Variable B : asyms.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := SK) (PI := PI_scene) B.
Hypothesis TCHECKX : tcheck_step_specX SK (PI := PI_scene) B.
(* -- reac_ctrl_build_scene_step.TAIL_TRAILER (0x20e20, 12 bytes), which build_scene_step's contract names at an
   accepting call site.  Its SHADOW: the entry statement's static facts of B, verbatim in substance
   (lib/A/P_LLVMFuzzerTestOneInput.v HB_Z_TT / HB_C_TT, with A_TAIL_TRAILER = 0x20e20 and TAIL_TRAILER_N = 12
   unfolded; two Theorem Labs lanes own them, a third owns the certificate). -- *)
Hypothesis HB_Z_TT : in_zs B (0x20e20 - 0x20) (0x20 + (12 - 12 mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly))
  (z1 (ANum (shadow_addr (0x20e20 + 8))) (12 mod 8)
   :: map (fun k => z1 (ANum (shadow_addr (0x20e20 + 8) + 1 + Z.of_nat k)) 0xf9) (seq 0 2)).
(* -- its BYTES: the entry statement's HRO_TT (at 0c703db40b0, a Theorem Labs lane's ruling of
   03:48Z), verbatim: [0x20e20, +12) is no owned static of B and not the errno cell.  With arodata_okS that gives
   the bytes; the image half (read-only segment, ROM bytes = scene_trailer) is s2_tt_img below. -- *)
Hypothesis HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
Variable WK : swalk.
(* -- the walk kit's read-only window is the listing's (a Theorem Labs lane's text, one across all lanes; the composition
   discharges both by eq_refl), and the walk's HSTK with LLVMF_SPDROP = 240 unfolded and LLVMF_STK = sw_stk WK: the
   deepest callee window below the realigned sp (memset's ESTACK, build_scene_step's 4144, check_step's 8496). -- *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
Hypothesis HSTK : 240 + ASTACK <= sw_stk WK.
(* the composition (walk HEV, LLVMF_EV = 6 <= EV_LIB): room for the one allocator event the journal has counted at
   C2, so check_step's `st_nev S + 0 <= EV_MAX` holds at its call (a Theorem Labs lane's text) *)
Hypothesis HWKev : 1 <= sw_ev WK.

Lemma s2_att : A_TT = 0x20e20.
Proof. vm_compute. reflexivity. Qed.
Lemma s2_lb1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
(* TAIL_TRAILER's shadow in every AR state, from HB_Z_TT / HB_C_TT (as a Theorem Labs lane's s2_trailer_shadow,
   lib/A/P_check_step_S2_aux.v:113-170, for check_step.trailer): cells 0x7fffc1c0 .. c4 = 0 (the zero range),
   c5 = 4 (the partial granule), c6, c7 = 0xf9. *)
Lemma s2_tt_shadow : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_TT 12 /\ shadow_hull_vis (aview SEGS (w_H W) mem) A_TT 12.
Proof.
  intros ly S W mem md HAR. rewrite s2_att.
  set (rd := aview SEGS (w_H W) mem).
  destruct HB_Z_TT as (q & m & Hin & Hq & Hm).
  destruct (zs_range _ _ q m Hin _ _ _ _ _ HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
  pose proof (zs_zero _ _ LAWS q m Hin _ _ _ _ _ HAR) as Hz.
  assert (ZR : forall x, 0x20e00 <= x < 0x20e28 -> rd (SHADOW_OFF + x / 8) = Some 0).
  { intros x Hx.
    replace (SHADOW_OFF + x / 8) with (shadow_of_addr SHADOW_OFF (q + (x - q)))
      by (unfold shadow_of_addr; f_equal; f_equal; lia).
    rewrite shadow_of_addr_aligned_off by exact Hq8. apply Hz.
    pose proof (Z.div_mod m 8 ltac:(lia)) as Dm.
    change (134688 - 32 + (32 + (12 - 12 mod 8))) with 134696 in Hm. change (134688 - 32) with 134656 in Hq.
    rewrite Hm8, Z.add_0_r in Dm. remember (m / 8) as m8 eqn:Em8.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. clear -Hx Hq Hm Dm. lia. }
  assert (CL : forall a v, In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> rd a = Some v).
  { intros a v Hin' Hv. pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin') as X.
    unfold cell_holds in X. cbn [z1 c1 c_at c_val c_w aeval] in X.
    specialize (X 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X.
    unfold rd. rewrite X. rewrite s2_lb1 by exact Hv. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) (HB_C_TT ly)) as HC.
  pose proof (HC _ ltac:(left; reflexivity)) as H5.
  pose proof (HC _ ltac:(right; cbn [map seq]; left; reflexivity)) as H6.
  pose proof (HC _ ltac:(right; cbn [map seq]; right; left; reflexivity)) as H7.
  assert (R5 : rd 0x7fffc1c5 = Some 4) by (apply CL; [exact H5 | lia]).
  assert (R6 : rd 0x7fffc1c6 = Some 0xf9) by (apply CL; [exact H6 | lia]).
  assert (R7 : rd 0x7fffc1c7 = Some 0xf9) by (apply CL; [exact H7 | lia]).
  pose proof (ZR 0x20e00 ltac:(lia)) as R0. pose proof (ZR 0x20e08 ltac:(lia)) as R1.
  pose proof (ZR 0x20e10 ltac:(lia)) as R2. pose proof (ZR 0x20e18 ltac:(lia)) as R3.
  pose proof (ZR 0x20e20 ltac:(lia)) as R4.
  change (SHADOW_OFF + 0x20e00 / 8) with 0x7fffc1c0 in R0. change (SHADOW_OFF + 0x20e08 / 8) with 0x7fffc1c1 in R1.
  change (SHADOW_OFF + 0x20e10 / 8) with 0x7fffc1c2 in R2. change (SHADOW_OFF + 0x20e18 / 8) with 0x7fffc1c3 in R3.
  change (SHADOW_OFF + 0x20e20 / 8) with 0x7fffc1c4 in R4.
  split.
  - intros x Hx. destruct (Z_lt_ge_dec x 0x20e28) as [Lx|Gx].
    + assert (E : shadow_of_addr SHADOW_OFF x = 0x7fffc1c4)
        by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
      exists 0. rewrite E. split; [exact R4 | unfold saddr_ok; left; reflexivity].
    + assert (E : shadow_of_addr SHADOW_OFF x = 0x7fffc1c5)
        by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
      exists 4. rewrite E. split; [exact R5 | unfold saddr_ok; right; split; Z.div_mod_to_equations; lia].
  - intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
    assert (Es : s = 0x7fffc1c0 \/ s = 0x7fffc1c1 \/ s = 0x7fffc1c2 \/ s = 0x7fffc1c3 \/
                 s = 0x7fffc1c4 \/ s = 0x7fffc1c5 \/ s = 0x7fffc1c6 \/ s = 0x7fffc1c7)
      by (revert Hs; Z.div_mod_to_equations; lia).
    destruct Es as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [rewrite R0 | rewrite R1 | rewrite R2 | rewrite R3 | rewrite R4 | rewrite R5 | rewrite R6 | rewrite R7];
      discriminate.
Qed.
(* TAIL_TRAILER's image half: the twelve addresses lie in a non-writable segment and their ROM bytes are
   scene_trailer's; closed facts of PI_scene's segments, decided by one vm_compute (a Theorem Labs lane measured 0.002 s). *)
Lemma s2_tt_img : forall i, 0 <= i < 12 ->
  in_roP SEGS pa_relro_lo pa_relro_hi (0x20e20 + i) /\
  option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 (0x20e20 + i))) =
  Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0))).
Proof.
  intros i Hi.
  assert (Hb : forallb (fun j =>
     existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? 0x20e20 + Z.of_nat j) &&
                         (0x20e20 + Z.of_nat j <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS &&
     match option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 (0x20e20 + Z.of_nat j))) with
     | Some v => v =? bv_unsigned (nth j scene_trailer (Z_to_bv 8 0)) | None => false end) (seq 0 12) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hb by lia. apply andb_prop in Hb as [H1 H2]. split.
  - left. apply existsb_exists in H1 as (s & Hs & Hc). exists s. split; [exact Hs|].
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hw Hlo].
    apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. split; [exact Hw | lia].
  - destruct (option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 (0x20e20 + i)))) as [v|];
      [apply Z.eqb_eq in H2; rewrite H2; reflexivity | discriminate].
Qed.
Let RUNP := SRr_run_pi_AJ (SK := SK) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (SK := SK) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI_scene).

(* reduce one `vat` clause of a cut to the register or spill-slot equation it stands for *)
Local Ltac vred H :=
  cbn [sg2_sp0 sg2_sp1 sg2_F sg2_Fsp sg2_shF sg2_shbase sg2_blki sg2_blk sg2_expect sg2_mac sg2_shexp
       sg2_body sg2_nprime sg2_Fb sg2_nn sg2_flags sg2_step sg2_s7v
       sg3_sp0 sg3_sp1 sg3_F sg3_Fb sg3_Fsp sg3_shF sg3_blki sg3_expect sg3_mac sg3_shexp
       sg3_body sg3_nn sg3_nprime sg3_flags sg3_step
       sg_cid sg_off_blk sg_off_blki sg_off_mac sg_off_expect scene_geom_asan] in H;
  cbv [vat RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 RV_a1 RV_a5 RV_a6 RV_a7] in H.

Theorem seg_S2 : seg_S2_stmt (SK := SK) SEGS B ameter_triv WK scene_geom_asan.
Proof.
unfold seg_S2_stmt. intros cx POST HBASE HC3 ly3 S3 W3 regs3 mem3 md3 bs body bb HCUT.
destruct HBASE as (HBASE0 & HSP1).
destruct HBASE0 as (HAFN & Hra & Ha0 & Ha1 & Hpn & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK & HFD & HFS & HMO).
assert (HROD0P : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)))
  by (rewrite <- HWRLO, <- HWRHI; exact HROD0).
destruct HCUT as (HJc & HAB & HBB & HBLK & HLBB & HGBB & HFRM & HSAV & HSHBG & HSHI & HSHB & HMACO
  & HIMG & HIN & HNN & HMAC
  & V_sp0 & V_sp1 & V_F & V_Fsp & V_shF & V_shbase & V_blki & V_blk & V_expect & V_mac & V_shexp
  & V_body & V_np & V_Fb & V_nn & V_flags & V_step & V_s7v).
(* n' and n'' are named before any reduction: `cbn [scene_geom_asan]` below would otherwise expand the table
   inside them and the two spellings would stop matching. *)
remember (sc_nprime scene_geom_asan bs) as npv eqn:Enpv.
remember (sc_nn scene_geom_asan bs) as nnv eqn:Ennv.
assert (Ennv2 : nnv = if npv =? 0 then 1 else npv) by (rewrite Ennv, Enpv; reflexivity).
(* ---- names and the facts every block of this segment uses ---- *)
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (EFe : sc_F SEGS scene_geom_asan cx = frame_addr (c_ly cx) 8 (c_fpos cx)) by reflexivity.
set (sp0 := spZ (c_regs cx)) in *.
set (sp1 := c_sp1 cx) in *.
set (fpos := c_fpos cx) in *.
set (F := sc_F SEGS scene_geom_asan cx) in *.
destruct HJc as (HJ & HFRS3 & HMOLE).
destruct HIMG as (HSP3 & HGP3 & HTP3 & HROD3).
destruct HAFN as (HAR0 & HraA & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfrs3 & Hnev3 & Hk3 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
assert (Hfin3 : In (8, fpos) (frames S3)) by (rewrite HFRS3; left; reflexivity).
assert (EFly : frame_addr ly3 8 fpos = F).
{ destruct Hly3 as (_ & _ & _ & _ & _ & EFa & _). rewrite EFe. unfold frame_addr. rewrite EFa. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 fpos HAR3 Hfin3) as (HF32 & _ & HFpres & HFSpres).
rewrite EFly in HF4096, HFceil, HFapp, HF32, HFpres, HFSpres.
change (fs_frame_bytes 8) with 16384 in HF4096, HFceil, HFapp, HFpres, HFSpres.
change (16384 / 8) with 2048 in HFSpres.
unfold shadow_addr in HFSpres.
assert (HF8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
set (sF := SHADOW_OFF + F / 8) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof alloc_ceiling_val as HACV0.
assert (HsFlo : 2147450880 + 512 <= sF) by (subst sF; unfold SHADOW_OFF;
  pose proof (Z.div_le_lower_bound F 8 512 ltac:(lia) ltac:(lia)); lia).
assert (HsFhi : sF + 2048 <= 17594333495296) by (subst sF; unfold SHADOW_OFF;
  pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (ECS : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
assert (EBW : SCENE_STEP_WIN = 4144) by (vm_compute; reflexivity).
assert (Ho1 : sp0 - 255 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0).
{ rewrite HSP1. pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as Hm.
  split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
destruct Ho1 as (Hob & Ho32).
assert (Ho16 : (sp1 - sp0) mod 16 = 0).
{ apply Z.mod_divide in Ho32; [|lia]. apply Z.mod_divide in Hal16; [|lia].
  destruct Ho32 as [q1 Hq1]. destruct Hal16 as [q2 Hq2].
  apply Z.mod_divide; [lia|]. exists (2 * q1 - q2). lia. }
assert (HWin : alloc_ceiling + 16624 <= sp0) by lia.
(* ---- the cut's values, with the table's projections reduced ---- *)
vred V_sp0. vred V_sp1. vred V_F. vred V_Fsp. vred V_shF. vred V_shbase. vred V_blki. vred V_blk.
vred V_expect. vred V_mac. vred V_shexp. vred V_body. vred V_np.  vred V_Fb. vred V_nn.
vred V_flags. vred V_step. vred V_s7v.
cbn [sg_sh_blki_lo sg_sh_blki_hi sg_sh_blk_lo sg_sh_blk_hi sg_off_blk sg_off_mac sg_off_blki sg_off_expect
  sg_blk_n sg_mac_n sg_scene_n sg_cid scene_geom_asan] in HSHI, HSHB, HMACO, HAB, HBB, HBLK, HLBB, HNN.
unfold sc_shr in HSHI, HSHB.
unfold sc_frame in HFRM. cbn [sg_cid scene_geom_asan] in HFRM.
change (fs_frame_bytes 8) with 16384 in HFRM.
destruct HFRM as (HFLAG & HFRMp & HFRMs).
(* ---- entry block: the symbolic state at C2, with the window of blk's five shadow cells ---- *)
unfold cfg_at. cbn [sg_pc_c2 scene_geom_asan].
replace (w64 (BASE + AF_LLVMFuzzerTestOneInput + SEG_C2_off))
  with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C2_off))) by (unfold w64; f_equal; lia).
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs3 []) E) by
  (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r) by
  (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E 19) = sF).
{ rewrite (EE 19%nat 19%bv eq_refl), V_shF. unfold shadow_addr, w64. apply unsigned_lit_small. unfold sF in *. lia. }
assert (HS : st_ok_pi SEGS VAL E
  (mkSS (AF_LLVMFuzzerTestOneInput + SEG_C2_off) sr_atoms
     [YP09.mkRegion (Some 19%nat) 18 23 18 23 []] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C2_off))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19 in Ha.
  right; right; right. exists 8, fpos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFly.
  change (fs_frame_bytes 8 / 8) with 2048. unfold sF in Ha. lia. }
(* ---- __asan_memset(blk, 0xa5, 34) at 0x82ce0 ---- *)
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (9%bv : bv 5) Rs1. prreg HS (21%bv : bv 5) Rs5. prreg HS (24%bv : bv 5) Rs8. prreg HS (27%bv : bv 5) Rs11.
prreg HS (18%bv : bv 5) Rs2. prreg HS (23%bv : bv 5) Rs7.
prreg HS (8%bv : bv 5) Rs0. prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (25%bv : bv 5) Rs9.
rewrite (EE 8%nat 8%bv eq_refl), V_sp0 in Rs0. rewrite (EE 19%nat 19%bv eq_refl), V_shF in Rs3.
rewrite (EE 20%nat 20%bv eq_refl), V_F in Rs4. rewrite (EE 25%nat 25%bv eq_refl), V_blki in Rs9.
rewrite (EE 9%nat 9%bv eq_refl), V_sp1 in Rs1.
rewrite (EE 17%nat 17%bv eq_refl), V_body in Rs5.
rewrite (EE 24%nat 24%bv eq_refl), V_np in Rs8.
rewrite (EE 27%nat 27%bv eq_refl), V_blk in Rs11.
rewrite (EE 23%nat 23%bv eq_refl), V_s7v in Rs7.
rewrite (EE 24%nat 24%bv eq_refl), V_np in Rs2.
rewrite (EE 27%nat 27%bv eq_refl), V_blk in Ra0.
rewrite (EE 2%nat 2%bv eq_refl) in Rsp. rewrite (EE 3%nat 3%bv eq_refl), HGP3 in Rgp.
rewrite (EE 4%nat 4%bv eq_refl), HTP3 in Rtp.
assert (EspA : spZ (ms_regs msA) = sp0 + (sp1 - sp0)).
{ replace (spZ (ms_regs msA)) with (spZ regs3) by (unfold spZ; rewrite Rsp; reflexivity). rewrite HSP3. lia. }
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict setpc ss_mem] in HRA.
assert (ZA : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) (ms_mem msA) (sF + j) = Some (if j =? 22 then 2 else 0)).
{ intros j Hj. assert (Hj' : j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | ->]]]]; cbn [Z.eqb Pos.eqb];
  (eapply s2_shb; [exact HRA | exact U19 | cbn; tauto | lia]). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sF + 18 <= a < sF + 23) ->
  aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. eapply s2_kept_run; [exact HFrA | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. rewrite U19 in Har. lia. }
clear HFrA HRA.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) AMEMSET W3 (ms_regs msA) (ms_mem msA)
    (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 _ 1
    (F + 144) 165 34 (sp1 - sp0) (Z_to_bv 64 (BASE + 1132)) HJA).
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia. - lia. - lia.
  - exact EspA.
  - exact Ho16. - lia. - rewrite Hes. lia.
  - exact Rgp. - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia].
    right; right; right. exists 8, fpos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFly. change (fs_frame_bytes 8) with 16384. lia.
  - unfold amem_range. unfold kHighMemBeg, kLowMemEnd, kHighMemEnd. lia.
  - replace (F + 144) with (F + 8 * 18) by lia. replace 34 with (8 * 4 + 2) by lia.
    apply s2_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. rewrite s2_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; lia). rewrite ZA by lia.
      destruct (Z.eqb_spec (18 + i) 22); [lia | reflexivity].
    + rewrite s2_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 18) + 4) with (sF + 22) by (unfold sF; lia). rewrite ZA by lia. reflexivity.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msA) _ 8 fpos (F + 144) 34 (proj1 HJA) Hfin3);
    [rewrite EFly; lia | rewrite EFly; change (fs_frame_bytes 8) with 16384; lia | lia].
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regsB & memB & mdB & -> & HJB & HPB & Ha0B & HeffB & HfrB & HpresB).
(* ---- run 2: 0x82ce4 .. jal reac_ctrl_build_scene_step (0x82cfc) ---- *)
rewrite Hes in HfrB.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 144 <= a < F + 178) -> ~ (sF + 18 <= a < sF + 23) ->
  ~ (sp1 - 4096 <= a < sp1) -> aview SEGS (w_H W3) memB a = aview SEGS (w_H W3) mem3 a).
{ intros a H1 H2 H3 H4. rewrite HfrB by lia. apply KA; lia. }
assert (KR9 : getr regsB 9%bv = getr (ms_regs msA) 9%bv) by exact (HPB 9 ltac:(unfold acallee_saved; lia)).
assert (KR18 : getr regsB 18%bv = getr (ms_regs msA) 18%bv) by exact (HPB 18 ltac:(unfold acallee_saved; lia)).
assert (KR21 : getr regsB 21%bv = getr (ms_regs msA) 21%bv) by exact (HPB 21 ltac:(unfold acallee_saved; lia)).
assert (KR23 : getr regsB 23%bv = getr (ms_regs msA) 23%bv) by exact (HPB 23 ltac:(unfold acallee_saved; lia)).
assert (KR24 : getr regsB 24%bv = getr (ms_regs msA) 24%bv) by exact (HPB 24 ltac:(unfold acallee_saved; lia)).
assert (KR27 : getr regsB 27%bv = getr (ms_regs msA) 27%bv) by exact (HPB 27 ltac:(unfold acallee_saved; lia)).
assert (KR2 : getr regsB 2%bv = getr (ms_regs msA) 2%bv) by exact (HPB 2 ltac:(unfold acallee_saved; lia)).
assert (KR3 : getr regsB 3%bv = getr (ms_regs msA) 3%bv) by exact (HPB 3 ltac:(unfold acallee_saved; lia)).
assert (KR4 : getr regsB 4%bv = getr (ms_regs msA) 4%bv) by exact (HPB 4 ltac:(unfold acallee_saved; lia)).
assert (KR8 : getr regsB 8%bv = getr (ms_regs msA) 8%bv) by exact (HPB 8 ltac:(unfold acallee_saved; lia)).
assert (KR19 : getr regsB 19%bv = getr (ms_regs msA) 19%bv) by exact (HPB 19 ltac:(unfold acallee_saved; lia)).
assert (KR20 : getr regsB 20%bv = getr (ms_regs msA) 20%bv) by exact (HPB 20 ltac:(unfold acallee_saved; lia)).
assert (KR25 : getr regsB 25%bv = getr (ms_regs msA) 25%bv) by exact (HPB 25 ltac:(unfold acallee_saved; lia)).
rewrite <- KR9 in Rs1. rewrite <- KR18 in Rs2. rewrite <- KR21 in Rs5. rewrite <- KR23 in Rs7.
rewrite <- KR24 in Rs8. rewrite <- KR27 in Rs11. rewrite <- KR2 in Rsp. rewrite <- KR3 in Rgp. rewrite <- KR4 in Rtp.
rewrite <- KR8 in Rs0. rewrite <- KR19 in Rs3. rewrite <- KR20 in Rs4. rewrite <- KR25 in Rs9.
clear KR8 KR19 KR20 KR25.
clear HS Ra0 Ra1 Ra2 Rra HE HEI EE HAG U19 E KR9 KR18 KR21 KR23 KR24 KR27 KR2 KR3 KR4.
set (stepv := sc_step bs mod 2 ^ 64) in *.
remember (Eimg (Ereg regsB [Z_to_bv 64 stepv])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsB [Z_to_bv 64 stepv]) E) by
  (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsB r) by
  (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 stepv).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsB [Z_to_bv 64 stepv] 0). }
assert (U9 : bv_unsigned (ew E 9) = sp1).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
pose proof alloc_ceiling_val as HACV.
pose proof HJB as (HARB & HlyB & _ & _ & _ & HfrsB & _ & _ & JB9 & JB10 & JB11 & JB12 & JB13 & JB14 & _).
assert (HSTEPB : rdword (aview SEGS (w_H W3) memB) (sp1 + 80) = Some stepv).
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_step|].
  intros q Hq. apply KB; lia. }
assert (HS : st_ok_pi SEGS VAL E
  (mkSS 1132 sr_atoms
     [YP09.mkRegion (Some 9%nat) 80 96 88 96 [YP09.mkChunk 80 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regsB (Z_to_bv 64 (BASE + 1132)) memB (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite U9. split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (apresent_writable SEGS). apply JB14. lia.
    + constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp1 80 8 (SOff 32 0) stepv).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (8 * Z.of_N 8) with 64. unfold stepv. apply Z.mod_pos_bound. lia.
      * change (Z.of_N 8) with 8. lia.
      * exact (val_mem_of_rdword SEGS _ _ _ _ HSTEPB).
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJB.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. left. lia. }
(* ---- reac_ctrl_build_scene_step(blk, body, n', step) at 0x82cfc ---- *)
rename ms into msC, HJB into HJC, HFr into HFrC. clear HF HG.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
prreg HS (13%bv : bv 5) Qa3. prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp.
prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite (EE 27%nat 27%bv eq_refl), Rs11 in Qa0.
rewrite (EE 21%nat 21%bv eq_refl), Rs5 in Qa1.
rewrite (EE 24%nat 24%bv eq_refl), Rs8 in Qa2.
rewrite E32 in Qa3.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Qsp.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Qgp. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Qtp.
assert (EspC : spZ (ms_regs msC) = sp0 + (sp1 - sp0)).
{ replace (spZ (ms_regs msC)) with (spZ regs3) by (unfold spZ; rewrite Qsp; reflexivity). rewrite HSP3. lia. }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 88 <= a < sp1 + 96) ->
  aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) memB a).
{ intros a Ha Hn. eapply s2_kept_run; [exact HFrC | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. rewrite U9 in Har. lia. }
pose proof HJC as (HARC & HlyC & _ & _ & _ & HfrsC & _ & _ & JC9 & JC10 & JC11 & JC12 & JC13 & JC14 & _).
assert (EFlyC : frame_addr ly3 8 fpos = F) by exact EFly.
(* blk's five shadow cells and the frame bytes, at the state the call starts from *)
assert (ZC : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) (ms_mem msC) (sF + j) = Some (if j =? 22 then 2 else 0)).
{ intros j Hj. rewrite KC by lia. rewrite HfrB by lia. apply ZA. lia. }
assert (HBLKC : forall i, 0 <= i < 34 -> aview SEGS (w_H W3) (ms_mem msC) (F + 144 + i) = Some 165).
{ intros i Hi. rewrite KC by lia. change 165 with (165 mod 256). apply HeffB. lia. }
assert (RAC : range_addressable (aview SEGS (w_H W3) (ms_mem msC)) SHADOW_OFF (F + 144) 34).
{ replace (F + 144) with (F + 8 * 18) by lia. replace 34 with (8 * 4 + 2) by lia.
  apply s2_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
  - intros i Hi. rewrite s2_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; lia). rewrite ZC by lia.
    destruct (Z.eqb_spec (18 + i) 22); [lia | reflexivity].
  - rewrite s2_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 18) + 4) with (sF + 22) by (unfold sF; lia). rewrite ZC by lia. reflexivity. }
destruct HNN as (HNN1 & HNN2).
assert (HNP : 0 <= npv <= 65535).
{ rewrite Enpv. unfold sc_nprime, sc_u16. cbn [sg_scene_n scene_geom_asan].
  destruct (HIN 1 ltac:(lia)) as (H1 & _). destruct (HIN 2 ltac:(lia)) as (H2 & _).
  destruct (Z.land (bs 0) 1 =? 0); lia. }
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem msC) _ 8 fpos HARC Hfin3) as (_ & _ & HFpresC & _).
rewrite EFly in HFpresC. change (fs_frame_bytes 8) with 16384 in HFpresC.
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem msC) _ 8 fpos HARC Hfin3) as HFimg.
rewrite EFly in HFimg. change (fs_frame_bytes 8) with 16384 in HFimg. unfold off_img in HFimg.
pose proof (pa_obj_img OBJ_TT ltac:(unfold OBJ_TT; lia)) as HTTimg.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem msC) _ body nnv 8 fpos HARC
  ltac:(rewrite HAB; apply in_or_app; right; left; reflexivity) Hfin3) as HSEPbf.
unfold zdisjoint in HSEPbf. cbn [fst snd] in HSEPbf. rewrite EFly in HSEPbf.
change (fs_frame_bytes 8) with 16384 in HSEPbf.
destruct HBLK as (HB4096 & HBz2 & HBceil & HBal & HBwr & HBtok).
pose proof (req_size_pos nnv ltac:(lia)) as (HRS1 & HRS2).
pose proof (zone2_band _ _ HBz2) as HBband.
assert (HBODYC : forall i, 0 <= i < nnv ->
  aview SEGS (w_H W3) (ms_mem msC) (body + i) = Some (bv_unsigned (nth (Z.to_nat i) bb (Z_to_bv 8 0)))).
{ intros i Hi. rewrite KC by lia. rewrite HfrB by lia. rewrite KA by lia.
  destruct (garr8_nthZ SEGS (mrestrict (w_H W3) mem3) body (u8s bb) i HGBB ltac:(lia)
    ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
  unfold u8s in Hv, Hr. rewrite (map_nth bv_unsigned bb (Z_to_bv 8 0)) in Hv, Hr.
  apply val_mem1_aview; [exact Hr | exact Hv]. }
pmkst HS.
rewrite pa_sigma_reac_ctrl_build_scene_step.
eapply SRr_bind.
{ eapply (BSS W3 (ms_regs msC) (ms_mem msC) _ (sw_stk WK) sp0 (sp1 - sp0) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(8, fpos)] ly3 S3 1 (F + 144) body npv stepv bb HJC).
  - exact EspC.
  - exact Ho16.
  - lia.
  - rewrite EBW. lia.
  - exact Qgp.
  - exact Qtp.
  - rewrite Qra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Qa0.
  - exact Qa1.
  - exact Qa2.
  - exact Qa3.
  - lia.
  - lia.
  - lia.
  - unfold stepv. pose proof (Z.mod_pos_bound (sc_step bs) (2 ^ 64) ltac:(lia)). lia.
  - intros HOK. destruct (okZ_true _ _ _ _ HOK) as (Hbk0 & Hbd0 & Hn8904 & Hst342).
    unfold SCENE_BYTES in Hn8904. unfold SCENE_LAST in Hst342.
    assert (Enn8 : nnv = 8904) by (rewrite Ennv2, <- Hn8904; destruct (Z.eqb_spec npv 0); lia).
    split.
    { exists 8, fpos. split; [left; reflexivity|]. split; [lia|].
      rewrite EFly. change (fs_frame_bytes 8) with 16384. unfold BLK_LEN. lia. }
    split.
    { intros a Ha. unfold BLK_LEN in Ha. apply (proj1 (HFpresC a ltac:(lia))). }
    split.
    { unfold BLK_LEN. exact RAC. }
    split.
    { apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem msC) _ 8 fpos (F + 144) BLK_LEN HARC Hfin3);
      [rewrite EFly; lia | rewrite EFly; change (fs_frame_bytes 8) with 16384; unfold BLK_LEN; lia | unfold BLK_LEN; lia]. }
    split.
    { exists body, nnv. split; [rewrite HAB; apply in_or_app; right; left; reflexivity|].
      split; [lia|]. unfold SCENE_BYTES. lia. }
    split.
    { unfold SCENE_BYTES. lia. }
    split.
    { intros i Hi. unfold SCENE_BYTES in Hi. apply HBODYC. lia. }
    destruct (s2_tt_shadow ly3 S3 W3 (ms_mem msC) _ HARC) as (HTT2 & HTT3).
    pose proof (arodata_ok_journalP (SK := SK) SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC HROD0P)
      as HRODC.
    split.
    { unfold TT_LEN. intros i Hi. rewrite s2_att.
      destruct (s2_tt_img i Hi) as (Hro & Hrom). destruct (HRO_TT i Hi) as (Hno & Hne).
      rewrite (HRODC (0x20e20 + i) Hro Hno Hne). exact Hrom. }
    split; [unfold TT_LEN; exact HTT2|].
    split; [unfold TT_LEN; exact HTT3|].
    unfold TT_LEN, BLK_LEN, A_TT. lia. }
cbv beta. intros W5 c5 _ (-> & regsD & memD & mdD & -> & HJD & HPD & HeffD & HpresD & HrD).
(* the three callee-saved registers the expected-return-value block reads: s2 (n' <> 8904), s7 (the sign of
   256 * b4) and s5 (step).  All survive the call. *)
prreg HS (18%bv : bv 5) Qs2. prreg HS (21%bv : bv 5) Qs5. prreg HS (23%bv : bv 5) Qs7.
prreg HS (9%bv : bv 5) Qs1. prreg HS (20%bv : bv 5) Qs4. prreg HS (19%bv : bv 5) Qs3.
prreg HS (25%bv : bv 5) Qs9. prreg HS (24%bv : bv 5) Qs8. prreg HS (27%bv : bv 5) Qs11b.
rewrite (EE 18%nat 18%bv eq_refl), Rs2 in Qs2.
rewrite E32 in Qs5.
rewrite (EE 23%nat 23%bv eq_refl), Rs7 in Qs7.
rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Qs1.
rewrite (EE 24%nat 24%bv eq_refl), Rs8 in Qs8.
rewrite (EE 27%nat 27%bv eq_refl), Rs11 in Qs11b.
rewrite (EE 20%nat 20%bv eq_refl), Rs4 in Qs4. rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Qs3.
rewrite (EE 25%nat 25%bv eq_refl), Rs9 in Qs9.
prreg HS (8%bv : bv 5) Qs0. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Qs0.
assert (KD18 : getr regsD 18%bv = getr (ms_regs msC) 18%bv) by exact (HPD 18 ltac:(unfold acallee_saved; lia)).
assert (KD21 : getr regsD 21%bv = getr (ms_regs msC) 21%bv) by exact (HPD 21 ltac:(unfold acallee_saved; lia)).
assert (KD23 : getr regsD 23%bv = getr (ms_regs msC) 23%bv) by exact (HPD 23 ltac:(unfold acallee_saved; lia)).
assert (KD9 : getr regsD 9%bv = getr (ms_regs msC) 9%bv) by exact (HPD 9 ltac:(unfold acallee_saved; lia)).
assert (KD20 : getr regsD 20%bv = getr (ms_regs msC) 20%bv) by exact (HPD 20 ltac:(unfold acallee_saved; lia)).
assert (KD19 : getr regsD 19%bv = getr (ms_regs msC) 19%bv) by exact (HPD 19 ltac:(unfold acallee_saved; lia)).
assert (KD25 : getr regsD 25%bv = getr (ms_regs msC) 25%bv) by exact (HPD 25 ltac:(unfold acallee_saved; lia)).
assert (KD24 : getr regsD 24%bv = getr (ms_regs msC) 24%bv) by exact (HPD 24 ltac:(unfold acallee_saved; lia)).
assert (KD27 : getr regsD 27%bv = getr (ms_regs msC) 27%bv) by exact (HPD 27 ltac:(unfold acallee_saved; lia)).
assert (KD8 : getr regsD 8%bv = getr (ms_regs msC) 8%bv) by exact (HPD 8 ltac:(unfold acallee_saved; lia)).
assert (KD2 : getr regsD 2%bv = getr (ms_regs msC) 2%bv) by exact (HPD 2 ltac:(unfold acallee_saved; lia)).
assert (KD3 : getr regsD 3%bv = getr (ms_regs msC) 3%bv) by exact (HPD 3 ltac:(unfold acallee_saved; lia)).
assert (KD4 : getr regsD 4%bv = getr (ms_regs msC) 4%bv) by exact (HPD 4 ltac:(unfold acallee_saved; lia)).
rewrite <- KD18 in Qs2. rewrite <- KD21 in Qs5. rewrite <- KD23 in Qs7. rewrite <- KD9 in Qs1.
rewrite <- KD20 in Qs4. rewrite <- KD19 in Qs3. rewrite <- KD25 in Qs9. rewrite <- KD24 in Qs8.
rewrite <- KD27 in Qs11b. rewrite <- KD8 in Qs0. rewrite <- KD2 in Qsp. rewrite <- KD3 in Qgp. rewrite <- KD4 in Qtp.
clear KD18 KD21 KD23 KD9 KD20 KD19 KD25 KD24 KD27 KD8 KD2 KD3 KD4.
(* ---- what memD keeps: the spill of body at [sp1 + 0x58] (written by run 2), the flags spill, blk's shadow ---- *)
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRC. cbn [ms_mem restrict setpc ss_mem] in HRC.
assert (HBODYSP : rdword (aview SEGS (w_H W3) (ms_mem msC)) (sp1 + 88) = Some body).
{ apply (rdword_of_val_mem SEGS); [|lia].
  exact (field_of_region E _ 9%nat sp1 _ 80 96 88 96 88 8 (SOff 21 0) body HRC U9 ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite (EE 21%nat 21%bv eq_refl), Rs5, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
clear HRC.
assert (HKD : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 144 <= a < F + 178) -> ~ (sp1 - 4144 <= a < sp1) ->
  aview SEGS (w_H W3) memD a = aview SEGS (w_H W3) (ms_mem msC) a).
{ intros a H1 H2 H3. apply HeffD; [exact H1 | rewrite EspC, EBW; lia | intros _; unfold BLK_LEN; lia]. }
assert (KD3 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 144 <= a < F + 178) -> ~ (sF + 18 <= a < sF + 23) ->
  ~ (sp1 - 4144 <= a < sp1) -> ~ (sp1 + 88 <= a < sp1 + 96) -> aview SEGS (w_H W3) memD a = aview SEGS (w_H W3) mem3 a).
{ intros a H1 H2 H3 H4 H5. rewrite HKD, KC, KB by lia. reflexivity. }
assert (HFLD : rdword (aview SEGS (w_H W3) memD) (sp1 + 72) = Some (sc_flags bs)).
{ rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_flags|]. intros q Hq. apply KD3; lia. }
assert (HBDD : rdword (aview SEGS (w_H W3) memD) (sp1 + 88) = Some body).
{ rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem msC))); [exact HBODYSP|]. intros q Hq. apply HKD; lia. }
assert (ZD : forall j, 18 <= j < 23 -> aview SEGS (w_H W3) memD (sF + j) = Some (if j =? 22 then 2 else 0)).
{ intros j Hj. rewrite HKD by lia. apply ZC. exact Hj. }
assert (HFL : 0 <= sc_flags bs < 256) by (unfold sc_flags; destruct (HIN 0 ltac:(lia)) as (H0 & _); lia).
clear HS HFrC HE HEI EE HAG E E32 U9.
(* ---- run 3: 0x82d00 .. the result check `bne a0, a1` at 0x82d28 ---- *)
rewrite Qra.
remember (Eimg (Ereg regsD [Z_to_bv 64 (sc_flags bs); Z_to_bv 64 body])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsD [Z_to_bv 64 (sc_flags bs); Z_to_bv 64 body]) E) by
  (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsD r) by
  (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (sc_flags bs)).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsD _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 body).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsD _ 1). }
assert (U9 : bv_unsigned (ew E 9) = sp1).
{ rewrite (EE 9%nat 9%bv eq_refl), Qs1. unfold w64. apply unsigned_lit_small. lia. }
assert (U27 : bv_unsigned (ew E 27) = F + 144).
{ rewrite (EE 27%nat 27%bv eq_refl), Qs11b. unfold w64. apply unsigned_lit_small. lia. }
(* ---- the expected-result value the check at 0x82d28 compares a0 with: a1 = -(s2 | (s7 < 0) | (step >= 343)), with
   s2 = snez (n' xor 8904) (0x82cc4-0x82ccc), s7 = sx16 (256 * b4), s5 = step (both sign-extended by slli/srai 48).
   It is 0 exactly when build_scene_step accepts. ---- *)
(* lia reads every hypothesis and splits every disjunction (an implication is one), so the facts of this block
   are proved and used in cleared contexts and dropped right after. *)
assert (HSTVr : 0 <= stepv < 2 ^ 64) by (change stepv with (sc_step bs mod 2 ^ 64); apply Z.mod_pos_bound; lia).
assert (E18 : ew E 18 = Z_to_bv 64 (if npv =? 8904 then 0 else 1)).
{ rewrite (EE 18%nat 18%bv eq_refl), Qs2.
  change (alu64 ALU_SLTU (Z_to_bv 64 0) (alu64 ALU_XOR (Z_to_bv 64 npv) (Z_to_bv 64 8904)) =
          Z_to_bv 64 (if npv =? 8904 then 0 else 1)).
  rewrite <- (s2a_snez_xor npv 8904) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
assert (HB34 : 0 <= bs 3 < 256 /\ 0 <= bs 4 < 256).
{ split; [destruct (HIN 3 ltac:(lia)) as (H0 & _) | destruct (HIN 4 ltac:(lia)) as (H0 & _)]; lia. }
assert (HS7 : -32768 <= sc_s7v bs < 32768 /\ (sc_s7v bs < 0 -> 128 <= bs 4) /\ (128 <= bs 4 -> sc_s7v bs < 0)).
{ clear - HB34. unfold sc_s7v, sx16. destruct (Z.ltb_spec (256 * bs 4) 32768); lia. }
assert (HST : -32768 <= sc_step bs < 32768 /\ (sc_step bs < 0 -> 128 <= bs 4) /\ (128 <= bs 4 -> sc_step bs < 0)).
{ clear - HB34. unfold sc_step, sx16. destruct (Z.ltb_spec (bs 3 + 256 * bs 4) 32768); lia. }
assert (HSTV : (0 <= sc_step bs -> stepv = sc_step bs) /\ (sc_step bs < 0 -> stepv = sc_step bs + 2 ^ 64)).
{ change stepv with (sc_step bs mod 2 ^ 64). clear - HST. split; intros H.
  - apply Z.mod_small. lia.
  - rewrite <- (Z_mod_plus_full (sc_step bs) 1 (2 ^ 64)). apply Z.mod_small. lia. }
assert (HA1 : U E (SAlu ALU_SUB (SLit 0)
    (SAlu ALU_OR
       (SAlu ALU_OR (SOff 18 0) (SAlu ALU_SLT (SAlu ALU_SRA (SAlu ALU_SLL (SOff 23 0) (SLit 48)) (SLit 48)) (SLit 0)))
       (SAlu ALU_XOR (SAlu ALU_SLT (SAlu ALU_SRA (SAlu ALU_SLL (SOff 21 0) (SLit 48)) (SLit 48)) (SLit 343)) (SLit 1))))
  = if scene_step_okZ (F + 144) body npv stepv then 0 else 2 ^ 64 - 1).
{ clear - EE Qs7 Qs5 E18 HNP HF4096 HB4096 HS7 HST HSTV HSTVr.
  destruct HS7 as (HS7r & HS7a & HS7b). destruct HST as (HSTr & HSTa & HSTb). destruct HSTV as (HSV1 & HSV2).
  rewrite (U_SAlu E ALU_SUB), (U_SAlu E ALU_OR (SAlu ALU_OR _ _)), (U_SAlu E ALU_OR (SOff 18 0)), (U_SAlu E ALU_XOR).
  rewrite (s2a_slt_sext16 E 23%nat (sc_s7v bs) 0); [| rewrite (EE 23%nat 23%bv eq_refl), Qs7; reflexivity | exact HS7r | lia].
  rewrite (s2a_slt_sext16 E 21%nat (sc_step bs) 343); [| rewrite (EE 21%nat 21%bv eq_refl), Qs5; reflexivity | exact HSTr | lia].
  rewrite (U_atom E 18%nat (if npv =? 8904 then 0 else 1) E18) by (destruct (npv =? 8904); lia).
  rewrite !U_SLit.
  unfold scene_step_okZ, SCENE_BYTES, SCENE_LAST.
  rewrite (proj2 (Z.eqb_neq (F + 144) 0)) by lia. rewrite (proj2 (Z.eqb_neq body 0)) by lia.
  destruct (Z.eqb_spec npv 8904) as [Hn|Hn]; destruct (Z.ltb_spec (sc_s7v bs) 0) as [H7|H7];
    destruct (Z.ltb_spec (sc_step bs) 343) as [H5|H5]; destruct (Z.leb_spec stepv 342) as [Hv|Hv];
    cbn [negb andb]; first [reflexivity | exfalso; lia]. }
clear HS7 HST HSTV HB34.
(* ---- the join at C3 0x82d74: both arms reach it with the journal of C2, the same heap, memD's frame, frame shadow,
   stack window and body, and these twelve registers.  cut_C3 is rebuilt here once. ---- *)
assert (JOIN : forall ly' S' W' regs' mem' md',
  ajournal (SK := SK) SEGS B (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, fpos)] ly' S' W' mem' md' 1 ->
  ablocks B ly' S' = ablocks B ly3 S3 ->
  (forall a, (F <= a < F + 16384) \/ (sF <= a < sF + 2048) \/ (sp1 <= a < sp0) \/ (body <= a < body + nnv) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) memD a) ->
  spZ regs' = sp1 -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  getr regs' 8 = w64 sp0 -> getr regs' 9 = w64 sp1 -> getr regs' 23 = w64 F -> getr regs' 20 = w64 F ->
  getr regs' 19 = w64 (shadow_addr F) -> getr regs' 25 = w64 (F + 32) -> getr regs' 24 = w64 npv ->
  getr regs' 11 = Z_to_bv 64 (sc_flags bs) -> getr regs' 21 = Z_to_bv 64 stepv ->
  SRr SEGS W' (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 1276)) mem' (seg_rom SEGS)) md') POST).
{ intros ly' S' W' regs' mem' md' HJ' HAB' HK' Q2 Q3 Q4 Q8 Q9 Q23 Q20 Q19 Q25 Q24 Q11 Q21.
  (* what mem' keeps of mem3, one region at a time: lia reads every hypothesis and splits every disjunction, so
     each separation is proved in a context cleared down to the bounds it uses *)
  clear Hpn HFimg HTTimg.
  assert (KMF : forall a, F <= a < F + 16384 -> ~ (F + 144 <= a < F + 178) ->
    aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha H1. rewrite (HK' a (or_introl Ha)). apply KD3; [clear - Ha HF4096 HFceil HACV; lia | exact H1
      | clear - Ha HFapp HsFlo HsFhi; lia | clear - Ha HFceil Hob HWin; lia | clear - Ha HFceil Hob HWin; lia]. }
  assert (KMS : forall a, sF <= a < sF + 2048 -> ~ (sF + 18 <= a < sF + 23) ->
    aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha H2. rewrite (HK' a (or_intror (or_introl Ha))).
    apply KD3; [clear - Ha HsFlo HsFhi; lia | clear - Ha HFapp HsFlo HsFhi; lia | exact H2
      | clear - Ha HsFhi HACV Hob HWin; lia | clear - Ha HsFhi HACV Hob HWin; lia]. }
  assert (KMP : forall a, sp1 <= a < sp0 -> ~ (sp1 + 88 <= a < sp1 + 96) ->
    aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha H3. rewrite (HK' a (or_intror (or_intror (or_introl Ha)))).
    apply KD3; [clear - Ha Hob HWin HACV Hshi H47; lia | clear - Ha HFceil Hob HWin; lia
      | clear - Ha HsFhi HACV Hob HWin; lia | clear - Ha; lia | exact H3]. }
  assert (KMB : forall a, body <= a < body + nnv -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. rewrite (HK' a (or_intror (or_intror (or_intror Ha)))).
    apply KD3; [clear - Ha HB4096 HBceil HRS2 HACV; lia | clear - Ha HSEPbf HRS2; lia
      | clear - Ha HBband HRS2 HsFlo HsFhi; lia | clear - Ha HBceil HRS2 Hob HWin; lia
      | clear - Ha HBceil HRS2 Hob HWin; lia]. }
  pose proof HJ' as (HAR' & Hly' & _ & _ & _ & Hfrs' & _).
  assert (Hfin' : In (8, fpos) (frames S')) by (rewrite Hfrs'; left; reflexivity).
  assert (EFly' : frame_addr ly' 8 fpos = F).
  { destruct Hly' as (_ & _ & _ & _ & _ & EFa & _). rewrite EFe. unfold frame_addr. rewrite EFa. reflexivity. }
  destruct (al_frames _ _ LAWS ly' S' W' mem' md' 8 fpos HAR' Hfin') as (_ & _ & HFpres' & HFSpres').
  rewrite EFly' in HFpres', HFSpres'. change (fs_frame_bytes 8) with 16384 in HFpres', HFSpres'.
  change (16384 / 8) with 2048 in HFSpres'.
  assert (EPC3 : sg_pc_c3 scene_geom_asan = BASE + 1276)
    by (cbn [sg_pc_c3 scene_geom_asan]; unfold SEG_C3_off, AF_LLVMFuzzerTestOneInput; lia).
  (* seat the goal in HC3's own spelling first: unifying `w64 pc` against `Z_to_bv 64 pc` inside `apply` ran 16 min *)
  replace (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 1276)) mem' (seg_rom SEGS)) md')
    with (cfg_at SEGS (sg_pc_c3 scene_geom_asan) regs' mem' md') by (unfold cfg_at; rewrite EPC3; reflexivity).
  apply (HC3 ly' S' W' regs' mem' md' bs body bb). clear HC3.
  unfold cut_C3. change (sc_F SEGS scene_geom_asan cx) with F. change (c_sp1 cx) with sp1.
  change (spZ (c_regs cx)) with sp0. change (c_fpos cx) with fpos. rewrite <- Ennv, <- Enpv.
  split.
  { unfold sc_j. split; [exact HJ'|]. split; [rewrite Hfrs', Hfr0; reflexivity | exact I]. }
  split; [rewrite HAB'; exact HAB|].
  split; [rewrite (blocks_bytes_bsum B ly' S'), HAB', <- (blocks_bytes_bsum B ly3 S3); exact HBB|].
  split; [exact (conj HB4096 (conj HBz2 (conj HBceil (conj HBal (conj HBwr HBtok)))))|].
  split; [exact HLBB|].
  split.
  { intros j Hj. pose proof Hj as Hj'. unfold u8s in Hj'. rewrite length_map in Hj'.
    destruct (HGBB j Hj) as (Hv & Hr). split; [|exact Hr].
    refine (proj1 (val_mem1_of_aview SEGS (w_H W') mem' (body + Z.of_nat j) _ _)).
    rewrite KMB by (clear - Hj' HLBB; lia). apply aview_of_val_mem1; [exact Hv | exact Hr]. }
  split.
  { unfold sc_frame. change (fs_frame_bytes (sg_cid scene_geom_asan)) with 16384. change (sc_F SEGS scene_geom_asan cx) with F.
    split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact HFLAG | intros q Hq; apply KMF; clear - Hq; lia]|].
    split; [intros a Ha; exact (proj1 (HFpres' a Ha))|].
    intros a Ha. change (16384 / 8) with 2048 in Ha. unfold shadow_addr in Ha |- *.
    replace a with (SHADOW_OFF + F / 8 + (a - (SHADOW_OFF + F / 8))) by ring.
    exact (proj1 (HFSpres' (a - (SHADOW_OFF + F / 8)) ltac:(clear - Ha; lia))). }
  split.
  { intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact (HSAV j Hj) | intros q Hq; apply KMP; clear - Hj Hq Hob; lia]. }
  split.
  { unfold sc_shbg in HSHBG |- *. cbn [sg_sh_bg scene_geom_asan] in HSHBG |- *.
    change (sc_F SEGS scene_geom_asan cx) with F in HSHBG |- *.
    apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) HSHBG t Ht) as Ht'.
    unfold sc_shr in Ht' |- *. intros o Ho. rewrite <- (Ht' o Ho).
    assert (Hotb : 0 <= o < 0x498 /\ ~ (18 <= o < 23)).
    { destruct Ht as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in Ho; lia. }
    assert (EsF : shadow_addr (sc_F SEGS scene_geom_asan cx) = sF) by reflexivity.
    rewrite EsF. apply KMS; clear - Hotb; lia. }
  split.
  { intros o Ho. cbn [sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan] in Ho. rewrite <- (HSHI o Ho).
    assert (EsF : shadow_addr (sc_F SEGS scene_geom_asan cx) = sF) by reflexivity.
    rewrite EsF. apply KMS; clear - Ho; lia. }
  split.
  { unfold sc_open. cbn [sg_off_blk sg_blk_n scene_geom_asan]. change (sc_F SEGS scene_geom_asan cx) with F.
    split; [rewrite Z.add_mod, HF8 by (clear; lia); reflexivity|]. split; [clear; lia|].
    intros i Hi. change ((34 + 7) / 8) with 5 in Hi. change (34 / 8) with 4. change (34 mod 8) with 2.
    unfold shadow_of_addr. replace (F + 144) with (F + 8 * 18) by ring. rewrite s2_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; ring).
    rewrite HK' by (right; left; clear - Hi; lia). rewrite ZD by (clear - Hi; lia).
    assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by (clear - Hi; lia).
    destruct Hi' as [-> | [-> | [-> | [-> | ->]]]]; reflexivity. }
  split.
  { unfold sc_open in HMACO |- *. cbn [sg_off_mac sg_mac_n scene_geom_asan] in HMACO |- *.
    change (sc_F SEGS scene_geom_asan cx) with F in HMACO |- *.
    destruct HMACO as (Hm8 & Hm0 & Hmc). split; [exact Hm8|]. split; [exact Hm0|].
    intros i Hi. rewrite <- (Hmc i Hi). change ((6 + 7) / 8) with 1 in Hi. assert (i = 0) as -> by (clear - Hi; lia).
    unfold shadow_of_addr. replace (F + 112) with (F + 8 * 14) by ring. rewrite s2_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 14) + 0) with (sF + 14) by (unfold sF; ring). apply KMS; clear; lia. }
  split.
  { unfold sc_img. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    rewrite HWRLO, HWRHI. exact (arodata_ok_journalP (SK := SK) SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HROD0P). }
  split; [exact HIN|].
  split; [clear - HNN1 HNN2; lia|].
  split.
  { cbn [sg_off_mac scene_geom_asan] in HMAC |- *. intros j Hj. destruct (HMAC j Hj) as (Hv & Hr). split; [|exact Hr].
    cbn [sc_macb length] in Hj.
    refine (proj1 (val_mem1_of_aview SEGS (w_H W') mem' (F + 112 + Z.of_nat j) _ _)).
    rewrite KMF by (clear - Hj; lia). apply aview_of_val_mem1; [exact Hv | exact Hr]. }
  cbn [sg3_sp0 sg3_sp1 sg3_F sg3_Fb sg3_Fsp sg3_shF sg3_blki sg3_expect sg3_mac sg3_shexp sg3_body sg3_nn sg3_nprime
       sg3_flags sg3_step sg_off_blki sg_off_mac sg_off_expect scene_geom_asan].
  cbv [vat RV_s0 RV_s1 RV_s3 RV_s4 RV_s5 RV_s7 RV_s8 RV_s9 RV_a1].
  split; [exact Q8|]. split; [exact Q9|]. split; [exact Q23|]. split; [exact Q20|].
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_Fsp | intros q Hq; apply KMP; clear - Hq Hob; lia]|].
  split; [exact Q19|]. split; [exact Q25|].
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_expect | intros q Hq; apply KMP; clear - Hq Hob; lia]|].
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_mac | intros q Hq; apply KMP; clear - Hq Hob; lia]|].
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_shexp | intros q Hq; apply KMP; clear - Hq Hob; lia]|].
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) memD)); [exact HBDD | intros q Hq; apply HK'; right; right; left; clear - Hq Hob; lia]|].
  split; [rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [exact V_nn | intros q Hq; apply KMP; clear - Hq Hob; lia]|].
  split; [exact Q24|]. split; [exact Q11|]. exact Q21. }
(* the arms need none of these, and lia reads every hypothesis *)
try clear Hpn. try clear HFimg. try clear HTTimg. try clear HSINK. try clear HFD. try clear HFS. try clear HMO. try clear HMOLE. try clear J9. try clear J10. try clear J11. try clear J12. try clear J13. try clear J14. try clear J15. try clear J16. try clear J17. try clear JB9. try clear JB10. try clear JB11. try clear JB12. try clear JB13. try clear JB14. try clear JC9. try clear JC10. try clear JC11. try clear JC12. try clear JC13. try clear JC14. try clear HARB. try clear HlyB. try clear HfrsB. try clear HlyC. try clear HfrsC. try clear HeffB. try clear HfrB. try clear HpresB. try clear HpresD. try clear KA. try clear KB. try clear KC. try clear ZA. try clear ZC. try clear HSHBG. try clear HSHI. try clear HSHB. try clear HMACO. try clear HMAC. try clear HFLAG. try clear HFRMp. try clear HFRMs. try clear HGBB. try clear HFpres. try clear HFSpres. try clear HFpresC. try clear V_sp0. try clear V_sp1. try clear V_F. try clear V_Fsp. try clear V_shF. try clear V_shbase. try clear V_blki. try clear V_blk. try clear V_expect. try clear V_mac. try clear V_shexp. try clear V_body. try clear V_np. try clear V_Fb. try clear V_nn. try clear V_flags. try clear V_step. try clear V_s7v. try clear HSTEPB. try clear HBODYSP. try clear Rs0. try clear Rs1. try clear Rs2. try clear Rs3. try clear Rs4. try clear Rs5. try clear Rs7. try clear Rs8. try clear Rs9. try clear Rs11. try clear Rsp. try clear Rgp. try clear Rtp. try clear RAC. try clear EspA. try clear EFlyC. 
destruct (scene_step_okZ (F + 144) body npv stepv) eqn:HOK.
- (* r = 0: build_scene_step accepted; the check at 0x82d28 falls through and beqz a0 (0x82d30) goes to
     check_step(blk, body, step) at 0x82d6c *)
  destruct HrD as (HrD0 & HrDblk).
  destruct (okZ_true _ _ _ _ HOK) as (_ & _ & Hn8904 & Hst342).
  unfold SCENE_BYTES in Hn8904. unfold SCENE_LAST in Hst342.
  assert (Enn8 : nnv = 8904) by (rewrite Ennv2, Hn8904; reflexivity).
  assert (HS0 : st_ok_pi SEGS VAL E
    (mkSS 1160 sr_atoms [YP09.mkRegion (Some 9%nat) 88 96 96 96 [YP09.mkChunk 88 (CVal 8 (SOff 33 0))]] None (mkFacts [] [] []))
    (restrict (w_H W3) (mkst regsD (Z_to_bv 64 (BASE + 1160)) memD (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp1 88 8 (SOff 33 0) body).
      * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (8 * Z.of_N 8) with 64. lia.
      * change (Z.of_N 8) with 8. lia.
      * exact (val_mem_of_rdword SEGS _ _ _ _ HBDD).
    - cbn. tauto.
    - unfold facts_ok; cbn; tauto. }
  assert (HS := st_ok_pi_pin_reg' E _ _ 10%bv 0 HS0 ltac:(cbn [restrict ms_regs mkst]; rewrite HrD0; reflexivity) eq_refl).
  clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_shc RUNP RUNC HS HJD.
  { intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  rename ms into msF, HFr into HFrF. clear HF HG.
  (* 0x82d28 bne a0, a1 -> abort: refuted, a0 = 0 = a1 *)
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ne_U, HA1 in Hc. rewrite U_lit in Hc by lia. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJD.
  { intros a (r & Hin & Ha). destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. lia. }
  rename ms into msE, HJD into HJE, HFr into HFrE. clear HF HG.
  prreg HS (10%bv : bv 5) Ea0. prreg HS (11%bv : bv 5) Ea1. prreg HS (12%bv : bv 5) Ea2. prreg HS (1%bv : bv 5) Era.
  prreg HS (2%bv : bv 5) Esp. prreg HS (3%bv : bv 5) Egp. prreg HS (4%bv : bv 5) Etp. prreg HS (8%bv : bv 5) Es0.
  prreg HS (9%bv : bv 5) Es1. prreg HS (19%bv : bv 5) Es3. prreg HS (20%bv : bv 5) Es4. prreg HS (21%bv : bv 5) Es5.
  prreg HS (23%bv : bv 5) Es7. prreg HS (24%bv : bv 5) Es8. prreg HS (25%bv : bv 5) Es9.
  rewrite (EE 27%nat 27%bv eq_refl), Qs11b in Ea0. rewrite E33 in Ea1. rewrite (EE 21%nat 21%bv eq_refl), Qs5 in Ea2.
  rewrite (EE 2%nat 2%bv eq_refl), Qsp in Esp. rewrite (EE 3%nat 3%bv eq_refl), Qgp in Egp.
  rewrite (EE 4%nat 4%bv eq_refl), Qtp in Etp. rewrite (EE 8%nat 8%bv eq_refl), Qs0 in Es0.
  rewrite (EE 9%nat 9%bv eq_refl), Qs1 in Es1. rewrite (EE 19%nat 19%bv eq_refl), Qs3 in Es3.
  rewrite (EE 20%nat 20%bv eq_refl), Qs4 in Es4. rewrite (EE 21%nat 21%bv eq_refl), Qs5 in Es5.
  rewrite (EE 20%nat 20%bv eq_refl), Qs4 in Es7. rewrite (EE 24%nat 24%bv eq_refl), Qs8 in Es8.
  rewrite (EE 25%nat 25%bv eq_refl), Qs9 in Es9.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msE) a = aview SEGS (w_H W3) memD a).
  { intros a Ha. transitivity (aview SEGS (w_H W3) (ms_mem msF) a).
    - eapply s2_kept_run; [exact HFrE | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har. lia.
    - eapply s2_kept_run; [exact HFrF | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. lia. }
  clear HFrE HFrF.
  pmkst HS.
  assert (EspE : spZ (ms_regs msE) = sp0 + (sp1 - sp0)).
  { replace (spZ (ms_regs msE)) with (spZ regs3) by (unfold spZ; rewrite Esp; reflexivity). rewrite HSP3. lia. }
  assert (Es0E : s0Z (ms_regs msE) = sp0) by (unfold s0Z; rewrite Es0; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
  pose proof HJE as (HARE & _ & _ & _ & _ & _ & _ & _ & JE9 & _).
  (* the caller chain at the call: LLVMFuzzerTestOneInput's frame record (sp0, ra, s0) pushed on the entry chain *)
  set (CH1 := if sp0 + 16 <? ly_top (c_ly cx) then [(sp0, raZ (c_regs cx), s0Z (c_regs cx))] else []).
  assert (HCH1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msE)) (sp0 + (sp1 - sp0)) (s0Z (ms_regs msE)) CH1).
  { rewrite Es0E. replace (sp0 + (sp1 - sp0)) with sp1 by lia.
    apply (achain_ly_top (c_ly cx) ly3); [first [exact Etop3 | symmetry; exact Etop3] |]. unfold CH1.
    destruct (Z.ltb_spec (sp0 + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
    - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ sp0 (s0Z (c_regs cx)) (raZ (c_regs cx)) [] sp1 Hch).
      + lia.
      + intros a Ha. apply JE9; lia.
      + rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [| intros q Hq; rewrite KE, KD3 by lia; reflexivity].
        replace (sp0 - 8) with (spZ (c_regs cx) - 8 - 8 * 0) by (unfold sp0; lia). exact (HSAV 0 ltac:(lia)).
      + rewrite (rdword_ext (aview SEGS (w_H W3) mem3)); [| intros q Hq; rewrite KE, KD3 by lia; reflexivity].
        replace (sp0 - 16) with (spZ (c_regs cx) - 8 - 8 * 1) by (unfold sp0; lia). exact (HSAV 1 ltac:(lia)).
      + exact Hra4.
      + lia.
      + clear - Hal16. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq].
        apply Z.mod_divide; [lia|]. exists (2 * q). lia.
      + lia.
      + lia.
    - left. split; [right; left; lia | reflexivity]. }
  assert (RAE : range_addressable (aview SEGS (w_H W3) (ms_mem msE)) SHADOW_OFF (F + 144) 34).
  { replace (F + 144) with (F + 8 * 18) by lia. replace 34 with (8 * 4 + 2) by lia.
    apply s2_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    - intros i Hi. rewrite s2_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 18) + i) with (sF + (18 + i)) by (unfold sF; lia). rewrite KE, ZD by lia.
      destruct (Z.eqb_spec (18 + i) 22); [lia | reflexivity].
    - rewrite s2_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 18) + 4) with (sF + 22) by (unfold sF; lia). rewrite KE, ZD by lia. reflexivity. }
  rewrite pa_sigma_check_step.
  eapply SRr_bind.
  { eapply (cl_callS (SK := SK) (PI := PI_scene) B LAWS W3 (ms_regs msE) (ms_mem msE) _ (sw_stk WK) sp0 [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(8, fpos)] ly3 S3 _ 1 TCHECK_STEP_STK [] EV_CHECK_STEP (sp1 - sp0) (Z_to_bv 64 (BASE + 1272)) CH1
      (fun ly' S' W' regs' mem' md' => ablocks B ly' S' = ablocks B ly3 S3) HJE).
    - exact EspE.
    - exact Ho16.
    - lia.
    - rewrite ECS. lia.
    - rewrite ECS. lia.
    - exact Egp.
    - exact Etp.
    - exact Era.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - exact HCH1.
    - intros HPRE2. eapply SRr_mono.
      + apply (TCHECKX ly3 S3 W3 (ms_regs msE) (ms_mem msE) _ CH1 (F + 144) body stepv bb HPRE2).
        * rewrite EspE. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Ho32.
        * rewrite EspE, Etop3. lia.
        * rewrite HFRS3. cbn. lia.
        * exact (arodata_ok_journalP (SK := SK) SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJE HROD0P).
        * exact Ea0.
        * exact Ea1.
        * exact Ea2.
        * unfold CS_LAST. lia.
        * apply (afobj_of_own SK SEGS B _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msE) _ 1 8 fpos (F + 144) CS_BLK_LEN HJE);
            unfold CS_BLK_LEN; [left; reflexivity | lia | rewrite EFly; lia | rewrite EFly; change (fs_frame_bytes 8) with 16384; lia
            | rewrite Z.add_mod, HF8 by lia; reflexivity | exact RAE].
        * unfold CS_BODY_LEN. rewrite HAB, <- Enn8. apply in_or_app. right. left. reflexivity.
        * unfold CS_BODY_LEN. apply Nat2Z.inj. rewrite Z2Nat.id by lia. lia.
        * intros i Hi. unfold CS_BODY_LEN in Hi. rewrite KE, HKD by lia. apply HBODYC. lia.
        * intros i Hi. unfold CS_BLK_LEN in Hi. rewrite KE by lia. apply HrDblk. unfold BLK_LEN. exact Hi.
        * unfold EV_CHECK_STEP. lia.
        * unfold LIVE_CHECK_STEP. pose proof (wf_live _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR3))) as HLV. lia.
      + intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ').
        exists ly', S', regs', mem', md'. split; [rewrite Era; reflexivity|]. split; [exact HJ'|].
        split; [exact HP' | exact HQ'].
    - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W6 c6 _ (ly6 & S6 & regsJ & memJ & mdJ & -> & HJJ & HJJ' & HPJ & HKJ).
  change (1 + EV_CHECK_STEP) with 1 in HJJ.
  pose proof HJJ' as (_ & _ & _ & _ & _ & _ & _ & _ & J9' & J10' & _ & J12' & _).
  assert (KJ : forall a, (F <= a < F + 16384) \/ (sF <= a < sF + 2048) \/ (sp1 <= a < sp0) \/ (body <= a < body + nnv) ->
    aview SEGS (w_H W6) memJ a = aview SEGS (w_H W3) memD a).
  { intros a Ha. rewrite <- (KE a) by lia. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    - apply (J12' 8 fpos a Hfin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFly;
        change (fs_frame_bytes 8) with 16384; lia | intros (r & Hr & _); destruct Hr].
    - apply (J12' 8 fpos a Hfin3); [right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFly;
        change (fs_frame_bytes 8 / 8) with 2048; unfold sF in Ha; lia | intros (r & Hr & _); destruct Hr].
    - apply J9'; [lia | rewrite ECS; lia].
    - replace a with (body + (a - body)) by lia.
      apply (J10' body nnv (a - body)); [rewrite HAB; apply in_or_app; right; left; reflexivity
        | rewrite HKJ, HAB; apply in_or_app; right; left; reflexivity | lia | intros (r & Hr & _); destruct Hr]. }
  clear HS HE HEI HAG EE E32 E33 U9 U27 E18 HA1 E.
  (* ---- run 4: 0x82d70 (ld a1, 0x48(s1)) .. C3 0x82d74 ---- *)
  remember (Eimg (Ereg regsJ [Z_to_bv 64 (sc_flags bs)])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg regsJ [Z_to_bv 64 (sc_flags bs)]) E) by
    (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsJ r) by
    (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (sc_flags bs)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsJ _ 0). }
  assert (P2 : getr regsJ 2%bv = getr (ms_regs msE) 2%bv) by exact (HPJ 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regsJ 3%bv = getr (ms_regs msE) 3%bv) by exact (HPJ 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regsJ 4%bv = getr (ms_regs msE) 4%bv) by exact (HPJ 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : getr regsJ 8%bv = getr (ms_regs msE) 8%bv) by exact (HPJ 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regsJ 9%bv = getr (ms_regs msE) 9%bv) by exact (HPJ 9 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regsJ 19%bv = getr (ms_regs msE) 19%bv) by exact (HPJ 19 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regsJ 20%bv = getr (ms_regs msE) 20%bv) by exact (HPJ 20 ltac:(unfold acallee_saved; lia)).
  assert (P21 : getr regsJ 21%bv = getr (ms_regs msE) 21%bv) by exact (HPJ 21 ltac:(unfold acallee_saved; lia)).
  assert (P23 : getr regsJ 23%bv = getr (ms_regs msE) 23%bv) by exact (HPJ 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regsJ 24%bv = getr (ms_regs msE) 24%bv) by exact (HPJ 24 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regsJ 25%bv = getr (ms_regs msE) 25%bv) by exact (HPJ 25 ltac:(unfold acallee_saved; lia)).
  assert (U9 : bv_unsigned (ew E 9) = sp1).
  { rewrite (EE 9%nat 9%bv eq_refl), P9, Es1. unfold w64. apply unsigned_lit_small. lia. }
  assert (HFLJ : rdword (aview SEGS (w_H W6) memJ) (sp1 + 72) = Some (sc_flags bs)).
  { rewrite (rdword_ext (aview SEGS (w_H W3) memD)); [exact HFLD | intros q Hq; apply KJ; lia]. }
  assert (HS : st_ok_pi SEGS VAL E
    (mkSS 1272 sr_atoms [YP09.mkRegion (Some 9%nat) 72 80 80 80 [YP09.mkChunk 72 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []))
    (restrict (w_H W6) (mkst regsJ (Z_to_bv 64 (BASE + 1272)) memJ (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp1 72 8 (SOff 32 0) (sc_flags bs)).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (8 * Z.of_N 8) with 64. lia.
      * change (Z.of_N 8) with 8. lia.
      * exact (val_mem_of_rdword SEGS _ _ _ _ HFLJ).
    - cbn. tauto.
    - unfold facts_ok; cbn; tauto. }
  paj_run_to_shc RUNTOP HS HJJ 1276.
  { intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  rename ms into msH, HFr into HFrH. clear HF HG.
  assert (KH : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W6) (ms_mem msH) a = aview SEGS (w_H W6) memJ a).
  { intros a Ha. eapply s2_kept_run; [exact HFrH | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. lia. }
  prreg HS (2%bv : bv 5) Hsp. prreg HS (3%bv : bv 5) Hgp'. prreg HS (4%bv : bv 5) Htp'. prreg HS (8%bv : bv 5) Hs0.
  prreg HS (9%bv : bv 5) Hs1. prreg HS (23%bv : bv 5) Hs7. prreg HS (20%bv : bv 5) Hs4. prreg HS (19%bv : bv 5) Hs3.
  prreg HS (25%bv : bv 5) Hs9. prreg HS (24%bv : bv 5) Hs8. prreg HS (11%bv : bv 5) Ha1'. prreg HS (21%bv : bv 5) Hs5.
  pmkst HS.
  apply (JOIN ly6 S6 W6 (ms_regs msH) (ms_mem msH) _ HJJ HKJ).
  + intros a Ha. rewrite KH by lia. apply KJ. exact Ha.
  + unfold spZ. rewrite Hsp, (EE 2%nat 2%bv eq_refl), P2, Esp. exact HSP3.
  + rewrite Hgp', (EE 3%nat 3%bv eq_refl), P3. exact Egp.
  + rewrite Htp', (EE 4%nat 4%bv eq_refl), P4. exact Etp.
  + rewrite Hs0, (EE 8%nat 8%bv eq_refl), P8. exact Es0.
  + rewrite Hs1, (EE 9%nat 9%bv eq_refl), P9. exact Es1.
  + rewrite Hs7, (EE 23%nat 23%bv eq_refl), P23. exact Es7.
  + rewrite Hs4, (EE 20%nat 20%bv eq_refl), P20. exact Es4.
  + rewrite Hs3, (EE 19%nat 19%bv eq_refl), P19. exact Es3.
  + rewrite Hs9, (EE 25%nat 25%bv eq_refl), P25. exact Es9.
  + rewrite Hs8, (EE 24%nat 24%bv eq_refl), P24. exact Es8.
  + rewrite Ha1'. exact E32.
  + rewrite Hs5, (EE 21%nat 21%bv eq_refl), P21. exact Es5.
- (* r <> 0: build_scene_step refused and left blk alone; the check at 0x82d28 falls through, beqz a0 does not
     jump, and the 34-turn loop 0x82d3c-0x82d50 finds every byte still 0xa5, so beqz a0 at 0x82d58 reaches C3 *)
  assert (HBLKD : forall i, 0 <= i < 34 -> aview SEGS (w_H W3) memD (F + 144 + i) = Some 165).
  { intros i Hi. rewrite HeffD; [apply HBLKC; exact Hi | lia | rewrite EspC, EBW; lia | intros H; discriminate H]. }
  assert (HS0 : st_ok_pi SEGS VAL E
    (mkSS 1160 sr_atoms [YP09.mkRegion (Some 9%nat) 72 80 80 80 [YP09.mkChunk 72 (CVal 8 (SOff 32 0))];
       YP09.mkRegion (Some 27%nat) 0 34 34 34 (map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit 165))) (seq 0 34))]
       None (mkFacts [] [] []))
    (restrict (w_H W3) (mkst regsD (Z_to_bv 64 (BASE + 1160)) memD (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ sp1 72 8 (SOff 32 0) (sc_flags bs)).
        * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (8 * Z.of_N 8) with 64. lia.
        * change (Z.of_N 8) with 8. lia.
        * exact (val_mem_of_rdword SEGS _ _ _ _ HFLD).
      + unfold region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
        rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
        apply (chunk_ok_val SEGS E _ (F + 144) (Z.of_nat i) 1 (SLit 165) 165); [reflexivity | cbn; lia | cbn; lia |].
        apply (proj1 (val_mem1_of_aview SEGS _ _ _ _ (HBLKD (Z.of_nat i) ltac:(lia)))).
    - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
      unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27. lia.
    - unfold facts_ok; cbn; tauto. }
  assert (HS := st_ok_pi_pin_reg' E _ _ 10%bv (2 ^ 64 - 1) HS0
    ltac:(cbn [restrict ms_regs mkst]; rewrite HrD; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) eq_refl).
  clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_shc RUNP RUNC HS HJD.
  { intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
  rename ms into msF, HFr into HFrF. clear HF HG.
  (* 0x82d28 bne a0, a1 -> abort: refuted, a0 = -1 = a1 *)
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ne_U, HA1 in Hc. rewrite U_lit in Hc by lia. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  (* the loop; its exit `j` to the abort at 0x82d5c is not taken: a0 folds to 0 *)
  paj_run_to_shc RUNTOP HS HJD 1276.
  { intros a (r & Hin & Ha). destruct Hin as [<- | [<- | []]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha; lia. }
  rename ms into msG, HFr into HFrG. clear HF HG.
  assert (KG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msG) a = aview SEGS (w_H W3) memD a).
  { intros a Ha. transitivity (aview SEGS (w_H W3) (ms_mem msF) a).
    - eapply s2_kept_run; [exact HFrG | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | [<- | []]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Har; lia.
    - eapply s2_kept_run; [exact HFrF | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | [<- | []]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har; lia. }
  prreg HS (2%bv : bv 5) Hsp. prreg HS (3%bv : bv 5) Hgp'. prreg HS (4%bv : bv 5) Htp'. prreg HS (8%bv : bv 5) Hs0.
  prreg HS (9%bv : bv 5) Hs1. prreg HS (23%bv : bv 5) Hs7. prreg HS (20%bv : bv 5) Hs4. prreg HS (19%bv : bv 5) Hs3.
  prreg HS (25%bv : bv 5) Hs9. prreg HS (24%bv : bv 5) Hs8. prreg HS (11%bv : bv 5) Ha1'. prreg HS (21%bv : bv 5) Hs5.
  pmkst HS.
  apply (JOIN ly3 S3 W3 (ms_regs msG) (ms_mem msG) _ HJD eq_refl).
  + intros a Ha. apply KG. lia.
  + unfold spZ. rewrite Hsp, (EE 2%nat 2%bv eq_refl), Qsp. exact HSP3.
  + rewrite Hgp', (EE 3%nat 3%bv eq_refl). exact Qgp.
  + rewrite Htp', (EE 4%nat 4%bv eq_refl). exact Qtp.
  + rewrite Hs0, (EE 8%nat 8%bv eq_refl). exact Qs0.
  + rewrite Hs1, (EE 9%nat 9%bv eq_refl). exact Qs1.
  + rewrite Hs7, (EE 20%nat 20%bv eq_refl). exact Qs4.
  + rewrite Hs4, (EE 20%nat 20%bv eq_refl). exact Qs4.
  + rewrite Hs3, (EE 19%nat 19%bv eq_refl). exact Qs3.
  + rewrite Hs9, (EE 25%nat 25%bv eq_refl). exact Qs9.
  + rewrite Hs8, (EE 24%nat 24%bv eq_refl). exact Qs8.
  + rewrite Ha1'. exact E32.
  + rewrite Hs5, (EE 21%nat 21%bv eq_refl). exact Qs5.
Qed.
End h.
End d.
Print Assumptions seg_S2.
