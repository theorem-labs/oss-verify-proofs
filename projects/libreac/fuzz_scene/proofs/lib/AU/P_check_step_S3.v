(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v, with its module paths changed; 410 of its 460 lines of code are new or changed and 160 lines of the source are left out. *)
(* Segment S3 of the ASan walk of check_step in fuzz_scene.asan-ubsan (sha256
   e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f): 0x8362c .. 0x836d4, proved here (a Theorem Labs lane)
   against the statement a Theorem Labs lane fixed. Rule 24 holds: this is ONE segment of the walk, not the function
   (the callees are Section hypotheses; the whole-function theorem is composed by cs_chain in P_check_step.v).
   C5: the unpoison stores of `frame`, `__asan_memcpy(F + 32, __const.check_step.frame, 50)` (0x8365c) and
   `__asan_memcpy(F + 48, blk, 34)` (0x83674) through aj_intrin_at (YCbq.v:1955), with the UBSan guard 0x83664
   decided from the frame's range fact; then the unpoison of `p`, reac_ctrl_parse (0x8369c, PARSE) in
   P_check_step_S3_mid.v (s3u_mid), and the five field checks plus reac_ctrl_checksum_verify (0x836cc, CKV through
   cl_callS, AU/Prog/YC85.v:384) in P_check_step_S3_aux.v (s3u_tail).
   Pre: the cut state at its first pc; post: cs_st4 at the next cut pc (P_check_step_cut.v).
   The 50-byte frame object is firstn 16 cs_frame_init ++ scene_block b k = s3_fr b k (P_check_step_S3_aux.v). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC4b YC45.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut P_check_step_S3_aux P_check_step_S3_mid.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96). *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by
   al_const (AR_const_law, YG0d.v:461-467), so no flag hypothesis is taken. *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane. *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
(* reac_ctrl_parse: a Theorem Labs lane (8cd86323565). *)
Hypothesis PARSE : tctrl_parse_spec (SK := SK) B.
(* reac_ctrl_checksum_verify (a Theorem Labs lane 33d26845cd2). *)
Hypothesis CKV : tctrl_checksum_verify_spec (SK := SK) B.
(* scene's start-up shadow of check_step's two globals as named facts of B (an internal review, CHECKSTEP-REVIEW item R2): full
   granules in as_zero_shadow, the partial granules and the f9 redzones as constant cells; the walk derives
   range_addressable and shadow_hull_vis from am_const (YG0n.v:211) and al_zshadow (YG0d.v:435-438), as cgif
   A/AE2m.v:20-54 does. shadow_addr 0x20d80 = 0x7fffc1b0, shadow_addr 0x20da0 = 0x7fffc1b4. *)
Hypothesis HB_Z_TR : Exists (zr_sub (A_CS_TRAILER, 8)) (as_zero_shadow B).
Hypothesis HB_Z_CF : Exists (zr_sub (A_CS_CFRAME, 48)) (as_zero_shadow B).
Hypothesis HB_C_CS : forall ly,
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_CFRAME + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr A_CS_CFRAME + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
(* static fact of the listing, closed by vm_compute on scene's PI: the two globals' addresses (same in both images); with HB_Z_TR / HB_Z_CF / HB_C_CS it pins every shadow byte of the 8-aligned hulls. *)
Hypothesis HB_ADDR : A_CS_TRAILER = 0x20d80 /\ A_CS_CFRAME = 0x20da0.
Hypothesis HRO_CF : ro_bytes SEGS pa_relro_lo pa_relro_hi B A_CS_CFRAME cs_frame_init.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
Definition s3_KL : list (bv 5) := [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition s3_keptL (regs regs' : bvmap 5 word) : Prop := forall r, In r s3_KL -> getr regs' r = getr regs r.
Lemma s3_keptL_of_pres : forall regs regs', aregs_preserved regs regs' -> s3_keptL regs regs'.
Proof.
intros regs regs' HP r Hr. unfold s3_KL in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ first
  [ exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact (HP 3 ltac:(unfold acallee_saved; lia))
  | exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact (HP 8 ltac:(unfold acallee_saved; lia))
  | exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact (HP 19 ltac:(unfold acallee_saved; lia))
  | exact (HP 21 ltac:(unfold acallee_saved; lia))
  | exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact (HP 23 ltac:(unfold acallee_saved; lia))
  | exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact (HP 25 ltac:(unfold acallee_saved; lia))
  | exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact (HP 27 ltac:(unfold acallee_saved; lia)) ] | ]).
destruct Hr.
Qed.
Lemma s3_keptL_trans : forall r1 r2 r3, s3_keptL r1 r2 -> s3_keptL r2 r3 -> s3_keptL r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma s3_agree : forall (regs : bvmap 5 word), env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Ltac inKL := unfold s3_KL; cbn [In]; repeat (first [left; reflexivity | right]).
Lemma s3_div8_add : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof.
intros x c Hx. rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hx, Z.add_0_r.
replace (8 * (x / 8) + 8 * c) with ((x / 8 + c) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma s3_ra_part : forall (rd : reader) a q r, a mod 8 = 0 -> 0 <= q -> 0 < r < 8 ->
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
  { rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r. replace (x - 8 * (a / 8)) with (x + (- (a / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Hdm. rewrite Eq in Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
- exists 0. split; [apply H0; lia | left; reflexivity].
Qed.
Lemma s3_kept_run : forall E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H mB a = aview SEGS H mA a.
Proof. intros E rs H mA mB a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma s3_shb : forall E (H : word -> bool) mem n b cs lo hi wlo whi od v,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
aview SEGS H mem (b + od) = Some v.
Proof.
intros E H mem n b cs lo hi wlo whi od v HR Hn Hc Hv.
apply aview_of_val_mem1; [|exact Hv]. exact (field_of_region E _ n b cs lo hi wlo whi od 1 (SLit v) v HR Hn Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma s3_const1 : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
In (z1 (ANum a) v) (as_const B ly) -> aview SEGS (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as X.
unfold cell_holds in X. cbn [c_at YG0f.c_val c_w aeval z1 c1] in X. specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X.
Qed.
Lemma s3_zs_byte : forall ly S (W : world SEGS) mem md a n x, AR SEGS B ly S W mem md ->
Exists (zr_sub (a, n)) (as_zero_shadow B) -> a <= x < a + n -> aview SEGS (w_H W) mem (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros ly S W mem md a n x HAR HE Hx. apply Exists_exists in HE as ((q & m) & Hin & Hsub). unfold zr_sub in Hsub. cbn [fst snd] in Hsub.
destruct (zs_range SEGS B q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
pose proof (zs_zero SEGS B LAWS q m Hin ly S W mem md HAR) as Hz.
assert (Ex : x / 8 = q / 8 + (x - q) / 8).
{ replace x with ((x - q) + (q / 8) * 8) at 1 by (pose proof (Z.div_mod q 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
rewrite Ex, Z.add_assoc. apply Hz. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod m 8 ltac:(lia)). lia.
Qed.
(* __const.check_step.frame's 50 bytes: shadow hull, addressability and image bytes, from the named B facts. *)
Lemma s3u_cf_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (aview SEGS (w_H W) mem) A_CS_CFRAME 50.
Proof.
intros ly S W mem md HAR s Hs. destruct HB_ADDR as [ET EC].
destruct (HB_C_CS ly) as (C1 & C2 & C3 & C4 & C5).
rewrite Forall_forall in C5.
assert (Hs' : 2147467696 <= s < 2147467712) by (rewrite EC in Hs; exact Hs).
assert (D1 : In (z1 (ANum 2147467697) 4) (as_const B ly)) by (rewrite ET in C1; exact C1).
assert (D2 : In (z1 (ANum 2147467698) 0xf9) (as_const B ly)) by (rewrite ET in C2; exact C2).
assert (D3 : In (z1 (ANum 2147467699) 0xf9) (as_const B ly)) by (rewrite ET in C3; exact C3).
assert (D4 : In (z1 (ANum 2147467706) 2) (as_const B ly)) by (rewrite EC in C4; exact C4).
assert (D7 : In (z1 (ANum 2147467707) 0xf9) (as_const B ly)) by (rewrite EC in C5; exact (C5 7 ltac:(cbn; tauto))).
assert (D8 : In (z1 (ANum 2147467708) 0xf9) (as_const B ly)) by (rewrite EC in C5; exact (C5 8 ltac:(cbn; tauto))).
assert (D9 : In (z1 (ANum 2147467709) 0xf9) (as_const B ly)) by (rewrite EC in C5; exact (C5 9 ltac:(cbn; tauto))).
assert (D10 : In (z1 (ANum 2147467710) 0xf9) (as_const B ly)) by (rewrite EC in C5; exact (C5 10 ltac:(cbn; tauto))).
assert (D11 : In (z1 (ANum 2147467711) 0xf9) (as_const B ly)) by (rewrite EC in C5; exact (C5 11 ltac:(cbn; tauto))).
clear Hs C1 C2 C3 C4 C5.
assert (Hc : s = 2147467696 \/ s = 2147467697 \/ s = 2147467698 \/ s = 2147467699 \/ 2147467700 <= s < 2147467706 \/
  s = 2147467706 \/ s = 2147467707 \/ s = 2147467708 \/ s = 2147467709 \/ s = 2147467710 \/ s = 2147467711) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [Hc | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
- replace 2147467696 with (SHADOW_OFF + A_CS_TRAILER / 8) by (rewrite ET; reflexivity).
  rewrite (s3_zs_byte ly S W mem md A_CS_TRAILER 8 A_CS_TRAILER HAR HB_Z_TR); [discriminate | lia].
- rewrite (s3_const1 ly S W mem md _ _ HAR D1). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D2). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D3). discriminate.
- replace s with (SHADOW_OFF + (A_CS_CFRAME + 8 * (s - 2147467700)) / 8).
  + rewrite (s3_zs_byte ly S W mem md A_CS_CFRAME 48 _ HAR HB_Z_CF); [discriminate | lia].
  + rewrite EC. rewrite s3_div8_add by reflexivity. unfold SHADOW_OFF. replace (134560 / 8) with 16820 by reflexivity. lia.
- rewrite (s3_const1 ly S W mem md _ _ HAR D4). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D7). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D8). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D9). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D10). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR D11). discriminate.
Qed.
Lemma s3u_cf_ra : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_CS_CFRAME 50.
Proof.
intros ly S W mem md HAR. destruct HB_ADDR as [ET EC].
destruct (HB_C_CS ly) as (_ & _ & _ & C4 & _).
change 50 with (8 * 6 + 2). apply s3_ra_part; [rewrite EC; reflexivity | lia | lia | |].
- intros i Hi. replace (SHADOW_OFF + A_CS_CFRAME / 8 + i) with (SHADOW_OFF + (A_CS_CFRAME + 8 * i) / 8)
    by (rewrite s3_div8_add by (rewrite EC; reflexivity); lia).
  apply (s3_zs_byte ly S W mem md A_CS_CFRAME 48 _ HAR HB_Z_CF). lia.
- unfold shadow_addr in C4. rewrite (s3_const1 ly S W mem md _ _ HAR C4). reflexivity.
Qed.
Lemma s3u_cf_bytes : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
forall i, 0 <= i < 50 -> aview SEGS (w_H W) mem (A_CS_CFRAME + i) = Some (bv_unsigned (nth (Z.to_nat i) cs_frame_init (Z_to_bv 8 0))).
Proof.
intros W mem HR i Hi. destruct (HRO_CF i ltac:(cbn; lia)) as (H1 & H2 & H3 & H4).
rewrite (HR _ H1 H2 H3). exact H4.
Qed.
(* ---- the walk: run, __asan_memcpy (F + 32 <- __const.check_step.frame, 50 B), the UBSan guard 0x83664,
   __asan_memcpy (F + 48 <- blk, 34 B), then a Theorem Labs lane's s3u_mid (parse) and a Theorem Labs lane's s3u_tail (field checks,
   reac_ctrl_checksum_verify, cs_st4). ---- *)
Lemma cs_S3 : CS_S3_stmt SK B.
Proof.
unfold CS_S3_stmt.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 HS3.
destruct HS3 as (HPRE & HFR & R19 & R21 & R24 & R22 & R23).
pose proof HFR as (HJ & HAB & HFLAG & HSAV & R2 & R3 & R4 & R8 & R18 & R25 & R26 & R27).
pose proof HPRE as (HAFN & Hal32 & Htop32 & Hlen7 & HROD & Ha0 & Ha1 & Ha2 & Hk & HFO & Hbody & Hlenb & Hbodyb & Hblkb & Hev & Hlive).
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR1 & Hly1 & Hsecs1 & Hwle1 & Hio1 & Hfrs1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (ESTK : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
change CS_CID with 2 in *. change CHECK_STEP_FRAME with 128 in *.
set (sp0 := spZ regs) in *.
set (F := frame_addr ly1 2 fpos) in *.
assert (Hfin1 : In (2, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly1 S1 W1 mem1 md1 2 fpos HAR1 Hfin1) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly1 S1 W1 mem1 md1 2 fpos HAR1 Hfin1) as (HF32 & _ & HFpres & HFSpres).
pose proof (frm_off_imgP B ly1 S1 W1 mem1 md1 2 fpos HAR1 Hfin1) as HFimg.
change (fs_frame_bytes 2) with 256 in *. fold F in HF4096, HFceil, HFapp, HF32, HFpres, HFSpres, HFimg.
change (256 / 8) with 32 in HFSpres.
unfold shadow_addr in HFSpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold off_img in HFimg.
destruct HB_ADDR as [ETR ECF].
assert (H8nz : 8 <> 0) by lia.
assert (HF8 : F mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in HF32; [|lia]; destruct HF32 as [q Hq]; exists (4 * q); lia).
assert (HFq : 8 * (F / 8) = F) by (pose proof (Z.div_mod F 8 H8nz); lia).
assert (HSB : 2147450880 + 512 <= SHADOW_OFF + F / 8 /\ SHADOW_OFF + F / 8 + 64 <= 17594333495296) by (unfold SHADOW_OFF; lia).
assert (Hsp0 : alloc_ceiling + 8496 <= sp0 <= 2 ^ 47) by (rewrite ESTK in Hslo; lia).
(* ---- run A: 0x8362c .. jal __asan_memcpy 0x8365c ---- *)
unfold cfg_at, CS_PC3, A_check_step.
replace (w64 (BASE + AF_check_step + 920)) with (Z_to_bv 64 (BASE + (AF_check_step + 920))) by (unfold w64; f_equal; lia).
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG : env_agree 32 (Ereg regs1 []) E) by (rewrite HE; apply s3_agree).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8) by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_check_step + 920) sr_atoms [YP09.mkRegion (Some 25%nat) 4 11 4 11 []] None (mkFacts [] [] []))
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + (AF_check_step + 920))) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres o ltac:(lia))).
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
  right; right; right. exists 2, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F.
  change (fs_frame_bytes 2 / 8) with 32. lia. }
rename ms into msA, HJ into HJA, HF into HFA, HFr into HFrA, HG into HGA.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
assert (ZA : forall j, 4 <= j < 10 -> aview SEGS (w_H W1) (ms_mem msA) (SHADOW_OFF + F / 8 + j) = Some 0).
{ intros j Hj. assert (Hj6 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia.
  destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
  (eapply s3_shb; [exact HRA | exact U25 | cbn; tauto | lia]). }
assert (TA : aview SEGS (w_H W1) (ms_mem msA) (SHADOW_OFF + F / 8 + 10) = Some 2)
  by (eapply s3_shb; [exact HRA | exact U25 | cbn; tauto | lia]).
clear HRA.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (20%bv : bv 5) Ra4.
assert (HspA : spZ (ms_regs msA) = sp0 - 128) by (unfold spZ; rewrite Rsp, (EE 2%nat 2%bv eq_refl), R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HRODA : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) (ms_mem msA)))
  by exact (arodata_ok_journalP SEGS _ _ pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJA HROD).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W1 (ms_regs msA) (ms_mem msA)
    TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly1 S1 _ 0 (F + 32) A_CS_CFRAME 50 (-128) (Z_to_bv 64 (BASE + 3516)) HJA).
  - rewrite Ra0, (EE 22%nat 22%bv eq_refl), R22. reflexivity.
  - rewrite Ra1. unfold A_CS_CFRAME, w64. change (A_OBJ 8) with 249%nat.
    rewrite <- (HEI 249%nat ltac:(cbv; lia)). symmetry. apply Z_to_bv_bv_unsigned.
  - exact Ra2.
  - lia. - lia. - lia.
  - rewrite HspA. lia.
  - reflexivity. - lia. - rewrite ESTK. unfold ESTACK. lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 2, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. fold F. change (fs_frame_bytes 2) with 256. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - change 50 with (8 * 6 + 2). apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. replace (F + 32) with (F + 8 * 4) by lia. rewrite s3_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 4) + i) with (SHADOW_OFF + F / 8 + (4 + i)) by lia. apply ZA. lia.
    + replace (F + 32) with (F + 8 * 4) by lia. rewrite s3_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 4) + 6) with (SHADOW_OFF + F / 8 + 10) by lia. exact TA.
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly1 S1 W1 _ _ 2 fpos); [exact (proj1 HJA) | exact Hfin1 | fold F; lia | fold F; change (fs_frame_bytes 2) with 256; lia | lia].
  - split; [rewrite ECF; lia|]. split; [rewrite ECF; lia|]. split.
    { intros a Ha. split.
      - replace a with (A_CS_CFRAME + (a - A_CS_CFRAME)) by lia. rewrite (s3u_cf_bytes W1 _ HRODA) by lia. discriminate.
      - rewrite HspA. rewrite ECF in Ha. unfold ESTACK. lia. }
    split; [rewrite ECF; lia|]. split; [unfold amem_range, kLowMemEnd; rewrite ECF; lia|].
    split; [exact (s3u_cf_ra _ _ _ _ _ (proj1 HJA))|]. intros _. exact (s3u_cf_hull _ _ _ _ _ (proj1 HJA)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff2 & Hkeep2 & Hpres2).
assert (KA : s3_keptL regs1 (ms_regs msA))
  by (intros r Hr; exact (regs_kept_of_st_ok SEGS E _ _ regs1 [] s3_KL HS HAG ltac:(vm_compute; reflexivity) r Hr)).
assert (A20 : getr regs2 20 = w64 2)
  by (transitivity (getr (ms_regs msA) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | rewrite Ra4; reflexivity]).
assert (K2 : s3_keptL regs1 regs2) by (eapply s3_keptL_trans; [exact KA | apply s3_keptL_of_pres; exact HP2]).
clear HS KA.
(* ---- run B: 0x83660 .. jal __asan_memcpy 0x83674 ---- *)
replace (VAL A_TEXT + 3516) with (BASE + (AF_check_step + 972)) by (unfold AF_check_step; lia).
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r) by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAG2 : env_agree 32 (Ereg regs2 []) E2) by (rewrite HE2; apply s3_agree).
assert (U22 : bv_unsigned (ew E2 22) = F + 32)
  by (rewrite (EE2 22%nat 22%bv eq_refl), (K2 22%bv ltac:(inKL)), R22; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E2 (mkSS (AF_check_step + 972) sr_atoms [] None (mkFacts [(22%nat, mkAF 4096 (2 ^ 47) 0)] [] []))
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 (BASE + (AF_check_step + 972))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22, Z.pow_0_r, Z.mod_1_r. lia. }
clear HE2.
paj_run_shc RUNP RUNC HS HJ2.
{ intros a (r & Hin & Ha). destruct Hin. }
rename ms into msB, HJ2 into HJB, HF into HFB, HFr into HFrB, HG into HGB.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2. prreg HS (1%bv : bv 5) Rbra.
prreg HS (2%bv : bv 5) Rbsp. prreg HS (3%bv : bv 5) Rbgp. prreg HS (4%bv : bv 5) Rbtp.
prreg HS (20%bv : bv 5) Rb20.
assert (KB : s3_keptL regs2 (ms_regs msB))
  by (intros r Hr; exact (regs_kept_of_st_ok SEGS E2 _ _ regs2 [] s3_KL HS HAG2 ltac:(vm_compute; reflexivity) r Hr)).
assert (K2B : s3_keptL regs1 (ms_regs msB)) by (eapply s3_keptL_trans; [exact K2 | exact KB]).
assert (B20 : getr (ms_regs msB) 20 = w64 2) by (rewrite Rb20, (EE2 20%nat 20%bv eq_refl); exact A20).
(* the frame's shadow bytes and the F+32 bytes survive memcpy 1 and run B *)
cbn [ss_mem] in HFB, HFrB.
assert (KRB : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem msB) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha. assert (Hnw : ~ in_wrange E2 [] a) by (intros (r0 & Hr0 & _); destruct Hr0).
  exact (s3_kept_run E2 [] (w_H W1) mem2 (ms_mem msB) a HFrB Ha Hnw). }
assert (SHB : forall j, 4 <= j <= 10 -> aview SEGS (w_H W1) (ms_mem msB) (SHADOW_OFF + F / 8 + j) = aview SEGS (w_H W1) (ms_mem msA) (SHADOW_OFF + F / 8 + j)).
{ intros j Hj.
  assert (Hr : 0 <= SHADOW_OFF + F / 8 + j < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
  rewrite (KRB (SHADOW_OFF + F / 8 + j) Hr).
  apply Hkeep2; [exact Hr | unfold SHADOW_OFF in *; lia | unfold ESTACK, SHADOW_OFF in *; lia]. }
assert (ZB : forall j, 4 <= j < 10 -> aview SEGS (w_H W1) (ms_mem msB) (SHADOW_OFF + F / 8 + j) = Some 0)
  by (intros j Hj; rewrite (SHB j ltac:(lia)); apply ZA; lia).
assert (TB : aview SEGS (w_H W1) (ms_mem msB) (SHADOW_OFF + F / 8 + 10) = Some 2)
  by (rewrite (SHB 10 ltac:(lia)); exact TA).
assert (CFB : forall i, 0 <= i < 16 -> aview SEGS (w_H W1) (ms_mem msB) (F + 32 + i) = Some (bv_unsigned (nth (Z.to_nat i) cs_frame_init (Z_to_bv 8 0)))).
{ intros i Hi.
  assert (Hr : 0 <= F + 32 + i < 2 ^ 64) by lia.
  rewrite (KRB (F + 32 + i) Hr). rewrite (Heff2 i ltac:(lia)).
  assert (Hi50 : 0 <= i < 50) by lia. exact (s3u_cf_bytes W1 _ HRODA i Hi50). }
(* blk: its frame, its bytes and its shadow at msB *)
destruct HFO as ((cidb & posb & Hinb & Hcidb & Hb8 & Hblo & Hbhi) & Hblk8 & HRAblk).
change CS_BLK_LEN with 34 in Hbhi, HRAblk.
assert (EFA : forall cid pos, frame_addr ly1 cid pos = frame_addr ly cid pos)
  by (intros cid pos; unfold frame_addr; destruct Hly1 as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (HinbS1 : In (cidb, posb) (frames S1)) by (rewrite Hfrs1; right; exact Hinb).
destruct (frames_bounds SEGS B LAWS ly1 S1 W1 (ms_mem msB) _ cidb posb (proj1 HJB) HinbS1) as (HB4096 & HBceil & HBapp).
rewrite EFA in HB4096, HBceil, HBapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HBapp.
assert (BLKB : forall i, 0 <= i < 34 -> aview SEGS (w_H W1) (ms_mem msB) (blk + i) = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))).
{ intros i Hi. pose proof HJB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cidb posb (blk + i) Hinb ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) ltac:(intros (r0 & [] & _))).
  exact (Hblkb i Hi). }
assert (HDIS : F + 48 + 34 <= blk \/ blk + 34 <= F + 48).
{ apply in_split in Hinb as (l2 & l3 & Hsp).
  pose proof (sep_frames_pos SEGS B LAWS ly1 S1 W1 (ms_mem msB) _ (2, fpos) (cidb, posb) [] l2 l3 (proj1 HJB)
    ltac:(cbn [app]; rewrite Hfrs1, Hsp; reflexivity)) as HD.
  unfold zdisjoint, frame_rng in HD. cbn [fst snd] in HD. rewrite (EFA cidb posb) in HD. fold F in HD.
  change (fs_frame_bytes 2) with 256 in HD. lia. }
(* ---- memcpy 2: F + 48 <- blk, 34 bytes (0x83674) ---- *)
assert (HspB : spZ (ms_regs msB) = sp0 - 128)
  by (unfold spZ; rewrite Rbsp, (EE2 2%nat 2%bv eq_refl), (K2 2%bv ltac:(inKL)), R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HRA48 : range_addressable (aview SEGS (w_H W1) (ms_mem msB)) SHADOW_OFF (F + 48) 34).
{ change 34 with (8 * 4 + 2). apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
  - intros i Hi. replace (F + 48) with (F + 8 * 6) by lia. rewrite s3_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 6) + i) with (SHADOW_OFF + F / 8 + (6 + i)) by lia. apply ZB. lia.
  - replace (F + 48) with (F + 8 * 6) by lia. rewrite s3_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 6) + 4) with (SHADOW_OFF + F / 8 + 10) by lia. exact TB. }
assert (HRAblkB : range_addressable (aview SEGS (w_H W1) (ms_mem msB)) SHADOW_OFF blk 34).
{ assert (HnF : forall x, inFP ([] : list (Z * Z)) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) by (intros x (r0 & Hr0 & _); destruct Hr0).
  exact (range_addressable_entry_frame SEGS B LAWS TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly1 S1 W1 (ms_mem msB) _ 0 cidb posb blk 34
    HJB Hinb Hcidb Hblo Hbhi Hb8 HnF HAR0 HRAblk). }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W1 (ms_regs msB) (ms_mem msB)
    TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly1 S1 _ 0 (F + 48) blk 34 (-128) (Z_to_bv 64 (BASE + 3540)) HJB).
  - rewrite Rb0, U22. unfold w64. f_equal. lia.
  - rewrite Rb1, (EE2 19%nat 19%bv eq_refl), (K2 19%bv ltac:(inKL)). exact R19.
  - exact Rb2.
  - lia. - lia. - lia.
  - rewrite HspB. lia.
  - reflexivity. - lia. - rewrite ESTK. unfold ESTACK. lia.
  - rewrite Rbgp, (EE2 3%nat 3%bv eq_refl), (K2 3%bv ltac:(inKL)), R3. exact Hgp.
  - rewrite Rbtp, (EE2 4%nat 4%bv eq_refl), (K2 4%bv ltac:(inKL)), R4. exact Htp.
  - exact Rbra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 2, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. fold F. change (fs_frame_bytes 2) with 256. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - exact HRA48.
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly1 S1 W1 _ _ 2 fpos); [exact (proj1 HJB) | exact Hfin1 | fold F; lia | fold F; change (fs_frame_bytes 2) with 256; lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - assert (Hd : 0 <= a - blk < 34) by lia. replace a with (blk + (a - blk)) by lia. rewrite (BLKB (a - blk) Hd). discriminate.
      - rewrite HspB. unfold ESTACK. lia. }
    split; [exact HDIS|]. split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
    split; [exact HRAblkB|]. intros _.
    eapply (shadow_hull_vis_of_frame SEGS B LAWS ly1 S1 W1 _ _ cidb posb); [exact (proj1 HJB) | exact HinbS1 | rewrite EFA; lia | rewrite EFA; lia | lia]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hkeep3 & Hpres3).
(* ---- what the two copies left at F + 32, and the cut facts at mem3 ---- *)
cbn [ss_mem] in HFA, HFrA.
assert (KRA : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 11) ->
  aview SEGS (w_H W1) (ms_mem msA) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hn. apply (s3_kept_run E _ (w_H W1) mem1 (ms_mem msA) a HFrA Ha).
  intros (r0 & Hr0 & Hr). cbn [In] in Hr0. destruct Hr0 as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U25 in Hr. lia. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 11) ->
  ~ (F + 32 <= a < F + 82) -> ~ (sp0 - 128 - ESTACK <= a < sp0 - 128) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha H1 H2 H3.
  assert (Hd3 : ~ (F + 48 <= a < F + 48 + 34)) by lia.
  assert (Hw3 : ~ (sp0 + -128 - ESTACK <= a < sp0 + -128)) by lia.
  assert (Hd2 : ~ (F + 32 <= a < F + 32 + 50)) by lia.
  rewrite (Hkeep3 a Ha Hd3 Hw3), (KRB a Ha), (Hkeep2 a Ha Hd2 Hw3). exact (KRA a Ha H1). }
assert (HFLAG3 : rdword (aview SEGS (w_H W1) mem3) (F + 256 - 8) = Some (flag_addr ly1 2 fpos)).
{ rewrite (rdword_ext (aview SEGS (w_H W1) mem1) (aview SEGS (w_H W1) mem3) (F + 256 - 8)); [exact HFLAG|].
  intros kk Hkk. apply KEEP; unfold ESTACK, SHADOW_OFF in *; lia. }
assert (HSAV3 : cs_saved regs (aview SEGS (w_H W1) mem3)).
{ intros j Hj. assert (HjZ : 0 <= Z.of_nat j <= 12) by lia.
  rewrite (rdword_ext (aview SEGS (w_H W1) mem1) (aview SEGS (w_H W1) mem3) (spZ regs - 8 - 8 * Z.of_nat j)); [exact (HSAV j Hj)|].
  intros kk Hkk. apply KEEP; unfold ESTACK, SHADOW_OFF in *; lia. }
assert (HLENB : length b = 8904%nat) by (rewrite Hlenb; reflexivity).
assert (HKR : 0 <= k <= 342) by (change CS_LAST with 342 in Hk; exact Hk).
assert (HBY : forall i, (i < 50)%nat -> aview SEGS (w_H W1) mem3 (F + 32 + Z.of_nat i) = Some (cp_v (s3_fr b k) i)).
{ intros i Hi. unfold cp_v. destruct (Nat.lt_ge_cases i 16) as [Hlo|Hhi].
  - assert (Hd3 : ~ (F + 48 <= F + 32 + Z.of_nat i < F + 48 + 34)) by lia.
    assert (Hw3 : ~ (sp0 + -128 - ESTACK <= F + 32 + Z.of_nat i < sp0 + -128)) by (unfold ESTACK in *; lia).
    assert (Hr : 0 <= F + 32 + Z.of_nat i < 2 ^ 64) by lia.
    assert (Hi16 : 0 <= Z.of_nat i < 16) by lia.
    rewrite (Hkeep3 (F + 32 + Z.of_nat i) Hr Hd3 Hw3), (CFB (Z.of_nat i) Hi16), (s3_fr_lo b k i Hlo), Nat2Z.id. reflexivity.
  - assert (Hj : 0 <= Z.of_nat i - 16 < 34) by lia.
    replace (F + 32 + Z.of_nat i) with (F + 48 + (Z.of_nat i - 16)) by lia.
    rewrite (Heff3 (Z.of_nat i - 16) Hj), (BLKB (Z.of_nat i - 16) Hj), (s3_fr_hi b k i HLENB HKR ltac:(lia)).
    do 2 f_equal. replace (Z.to_nat (Z.of_nat i - 16)) with (i - 16)%nat by lia. reflexivity. }
assert (SH3 : forall j, 4 <= j <= 10 -> aview SEGS (w_H W1) mem3 (SHADOW_OFF + F / 8 + j) = aview SEGS (w_H W1) (ms_mem msB) (SHADOW_OFF + F / 8 + j)).
{ intros j Hj. apply Hkeep3; unfold ESTACK, SHADOW_OFF in *; lia. }
assert (HRA32 : range_addressable (aview SEGS (w_H W1) mem3) SHADOW_OFF (F + 32) 50).
{ change 50 with (8 * 6 + 2). apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
  - intros i Hi. replace (F + 32) with (F + 8 * 4) by lia. rewrite s3_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 4) + i) with (SHADOW_OFF + F / 8 + (4 + i)) by lia.
    assert (Hj : 4 <= 4 + i <= 10) by lia. rewrite (SH3 (4 + i) Hj). apply ZB. lia.
  - replace (F + 32) with (F + 8 * 4) by lia. rewrite s3_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 4) + 6) with (SHADOW_OFF + F / 8 + 10) by lia.
    assert (Hj : 4 <= 10 <= 10) by lia. rewrite (SH3 10 Hj). exact TB. }
assert (K3 : s3_keptL regs1 regs3) by (eapply s3_keptL_trans; [exact K2B | apply s3_keptL_of_pres; exact HP3]).
assert (R20_3 : getr regs3 20 = w64 2)
  by (transitivity (getr (ms_regs msB) 20); [exact (HP3 20 ltac:(unfold acallee_saved; lia)) | exact B20]).
assert (HFR3 : cs_frame SK B regs ly S W mem md fpos ly1 S1 W1 regs3 mem3 md3).
{ unfold cs_frame. change CS_CID with 2. change (fs_frame_bytes 2) with 256. fold F.
  split; [exact HJ3|]. split; [exact HAB|]. split; [exact HFLAG3|]. split; [exact HSAV3|].
  split; [rewrite (K3 2%bv ltac:(inKL)); exact R2|]. split; [rewrite (K3 3%bv ltac:(inKL)); exact R3|].
  split; [rewrite (K3 4%bv ltac:(inKL)); exact R4|]. split; [rewrite (K3 8%bv ltac:(inKL)); exact R8|].
  split; [rewrite (K3 18%bv ltac:(inKL)); exact R18|]. split; [rewrite (K3 25%bv ltac:(inKL)); exact R25|].
  split; [rewrite (K3 26%bv ltac:(inKL)); exact R26|]. rewrite (K3 27%bv ltac:(inKL)); exact R27. }
(* ---- 0x83678 .. 0x836a0 (a Theorem Labs lane's s3u_mid), then 0x836a0 .. the cut (a Theorem Labs lane's s3u_tail) ---- *)
replace (Z_to_bv 64 (BASE + 3540)) with (w64 (A_check_step + 0x3e4))
  by (unfold w64, A_check_step, AF_check_step; f_equal; lia).
eapply SRr_bind.
{ refine (s3u_mid SK B PARSE ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs3 mem3 md3 HPRE HFR3 R20_3 _ _ _ _ HBY HRA32).
  - rewrite (K3 21%bv ltac:(inKL)); exact R21.
  - rewrite (K3 24%bv ltac:(inKL)); exact R24.
  - change CS_CID with 2. fold F. rewrite (K3 22%bv ltac:(inKL)); exact R22.
  - change CS_CID with 2. fold F. rewrite (K3 23%bv ltac:(inKL)); exact R23. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
exact (s3u_tail SK B CKV ly S W regs mem md ch blk body k b fpos ly4 S4 W4 regs4 mem4 md4 HPRE P1 P2 P3 P4 P5 P6 P7 P8 P9 P10).
Qed.
End h.
End f.
End d.
Print Assumptions cs_S3.
