(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1kx X1el X1ec. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1my X1nc X1ne X1ni X1nf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition oblk (r : option bptr) (A n : Z) : list block := match r with None => [] | Some p => [(p, A, n)] end.
Lemma present_cons : forall (r : option bptr) o (A n : Z) ad ns, present (r :: o) (A :: ad) (n :: ns) = oblk r A n ++ present o ad ns.
Proof. destruct r; reflexivity. Qed.

Definition rcalloc_opost {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem) (r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (A : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m' /\ ps_so s' = ps_so s
/\ RHEAP s' (oblk r A n ++ LB) m'
/\ (r = None -> A = 0)
/\ (forall p, r = Some p -> rblock_range A n /\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]).

Lemma rcalloc_opt {RCEIL : RunCeiling} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (m0 lo B : Z) (errv : word),
RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 m0 -> a1 = Z_to_bv 64 1 -> 0 <= m0 <= RSMALL_MAX ->
implM rsegs (raw_calloc m0 1) s (rcalloc_opost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB m0 lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom rsegs)).
Proof.
intros. eapply implM_mono.
{ eapply (rcalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LB m0 1 lo B errv); try eassumption; unfold RSMALL_MAX in *; lia. }
cbv beta. intros r s' ms' sfH_; first [ sf_destruct 26%nat sfH_ as x0 x1 x2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x3 x4 x5 x6 m' errv' -> MI' ST' ERR' AUX' HP' PSF' PSO' RES | sf_fb; destruct sfH_ as (x0 & x1 & x2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & PSF' & PSO' & RES) ].
rewrite Z.mul_1_l in RES. unfold rcalloc_opost.
destruct r as [p|].
- first [ sf_destruct 6%nat RES as A -> BR HEAP' Z0 _ | sf_fb; destruct RES as (A & -> & BR & HEAP' & Z0 & _) ]. exists A. sf_eexists 14%nat. exists m', errv'.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact HP'|]. split; [exact PSO'|].
split; [exact HEAP'|]. split; [intros; discriminate|]. intros q _. split; assumption.
- destruct RES as [-> HEAP']. exists 0. sf_eexists 14%nat. exists m', errv'.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact HP'|]. split; [exact PSO'|].
split; [exact HEAP'|]. split; [reflexivity|]. intros q E; discriminate E.
Qed.

Lemma decst_rep_rheap : forall d OUT STEREO m m' SL L LBIG SP,
DREP OUT STEREO m SL d L -> rheap_pres LBIG SP m m' -> (forall b, In b L -> In b LBIG) -> DREP OUT STEREO m' SL d L.
Proof.
intros d OUT STEREO m m' SL L LBIG SP R HP SUB. eapply decst_rep_agree; [exact R|].
intros a Ha (b & Hb & Hab). apply HP; [exact Ha|]. right. right. exists b. split; [apply SUB; exact Hb| exact Hab].
Qed.

Lemma f32_zeros_bytes : forall k, cells_bytes (f32 (repeat (Z_to_bv 64 0) k)) = repeat (Z_to_bv 8 0) (4 * k).
Proof.
induction k as [|k IH]; [reflexivity|]. cbn [repeat]. rewrite f32_cons. cbn [cells_bytes cbytes app].
replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [repeat]. rewrite <- IH. reflexivity.
Qed.
Lemma zero_f32_recast : forall m A n, 0 <= n ->
rw_cells rsegs m A [CB (Z.to_nat (n * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (n * 4)))] -> rw_cells rsegs m A (f32 (repeat (Z_to_bv 64 0) (Z.to_nat n))).
Proof.
intros m A n Hn X. apply (X0pw.rw_cells_recast rsegs m A _ _ X).
- apply cells_wf_f32.
- rewrite f32_zeros_bytes. cbn [cells_bytes cbytes app]. rewrite app_nil_r. f_equal. lia.
- rewrite cells_size_f32, repeat_length. cbn. lia.
Qed.

Definition sb_init_fin (mo : spx_mode) (blk : bptr) (lr : Z) (low : dec_state bptr) (g0 g1 ex oq iq pg er ms : option bptr)
: M PState (option (dec_state bptr)) :=
let frame_size := sbm_frameSize mo in
let subframeSize := sbm_subframeSize mo in
let nbSubframes := Z.quot frame_size subframeSize in
let lpcSize := sbm_lpcSize mo in
let sampling_rate := lr * 2 in
match g0, g1, ex, oq, iq, pg, er, ms with
| Some g0, Some g1, Some ex, Some oq, Some iq, Some pg, Some er, Some ms =>
mret (Some (DecSB (mkSBD blk mo (2 * frame_size) frame_size subframeSize nbSubframes lpcSize
1 sampling_rate 0 g0 g1 ex oq iq ms pg er None 1 (sbm_defaultSubmode mo)) low))
| _, _, _, _, _, _, _, _ => munr
end.
Lemma sb_init_rest_eq : forall mo blk lr low,
sb_init_rest mo blk lr low =
(g0 <- raw_calloc (QMF_ORDER * 4) 1 ;; g1 <- raw_calloc (QMF_ORDER * 4) 1 ;;
ex <- raw_calloc (sbm_subframeSize mo * 4) 1 ;; oq <- raw_calloc (sbm_lpcSize mo * 4) 1 ;; iq <- raw_calloc (sbm_lpcSize mo * 4) 1 ;;
pg <- raw_calloc (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) 1 ;; er <- raw_calloc (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) 1 ;;
ms <- raw_calloc (2 * sbm_lpcSize mo * 4) 1 ;;
sb_init_fin mo blk lr low g0 g1 ex oq iq pg er ms).
Proof. reflexivity. Qed.

Theorem rinit_sbB {RCEIL : RunCeiling} : forall (mo : spx_mode)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(s : PState) (LB : list block) (AB lo : Z) (m0 : mem),
(mo = ModeWB \/ mo = ModeUWB) ->
bv_unsigned sp <= AB -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - init_depth mo -> tp = Z_to_bv 64 RATP ->
forall blk S lr low LBL st ms,
sb_at78 mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB AB lo m0 blk S lr low LBL st ms ->
implM rsegs (sb_init_rest mo blk lr low) st (rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m0) ms.
Proof.
intros mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB AB lo m0 Hmo SB CLO LO TPE blk S lr low LBL st_0 ms sfH_; first [ sf_destruct 42%nat sfH_ as t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F0 fc m_0 errv_0 j4 tmp SL -> FRM MI_0 ST_0 FR_0 ERR_0 AUX_0 PRES_0 PSO_0 TP_0 HEAP_0 BR SLB X_0 RL_0 DM DD ELR STO NES | sf_fb; destruct sfH_ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F0 & fc & m_0 & errv_0 & j4 & tmp & SL & -> & FRM & MI_0 & ST_0 & FR_0 & ERR_0 & AUX_0 & PRES_0 & PSO_0 & TP_0 & HEAP_0 & BR & SLB & X_0 & RL_0 & DM & DD & ELR & STO & NES) ].
pose proof (mode_facts mo Hmo) as sfP_; first [ sf_destruct 7%nat sfP_ as FSS LPC NBS DSM IDP IRT MDP | sf_fb; destruct sfP_ as (FSS & LPC & NBS & DSM & IDP & IRT & MDP) ]. rewrite IDP in LO.
assert (SUBR : 0 <= sbm_subframeSize mo * 4 <= 320) by (destruct FSS as [[_ E]|[_ E]]; rewrite E; lia). clear FSS.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR_0. unfold RERRNO in ERR_0.
assert (IDL : 8272 <= init_depth (lower_mode mo)) by (destruct Hmo as [-> | ->]; cbn; lia).
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as S0 S16 _ SCE SIMG | sf_fb; destruct sfP_ as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling, SBSTATE_SIZEOF in SCE. unfold SBSTATE_SIZEOF in SIMG.
assert (SLT : S + 160 <= bv_unsigned sp + -48) by lia.

pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_0) as ND.
assert (SAPL : forall b, In b LBL -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S).
{ intros b Hb. destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP_0 ltac:(left; reflexivity) ltac:(right; apply in_app_iff; left; exact Hb)) as [D|D].
{ intros E. cbn [map app] in ND. apply (proj1 (List.NoDup_cons_iff _ _)) in ND. destruct ND as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. rewrite map_app. apply in_app_iff. left. apply in_map. exact Hb. }
all: cbn [blk_addr blk_size fst snd] in D |- *; unfold SBSTATE_SIZEOF in D; lia. }
assert (BRL : forall b, In b LBL -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; eapply RHEAP_block_range_proof; [exact HEAP_0| right; apply in_app_iff; left; exact Hb]).
assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling /\ (S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S)).
{ intros b Hb. split.
- first [ pose proof (RHEAP_block_range_proof _ _ _ _ HEAP_0 ltac:(right; apply in_app_iff; right; exact Hb)) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ _ HEAP_0 ltac:(right; apply in_app_iff; right; exact Hb)) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia.
- destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP_0 ltac:(left; reflexivity) ltac:(right; apply in_app_iff; right; exact Hb)) as [D|D].
{ intros E. cbn [map app] in ND. apply (proj1 (List.NoDup_cons_iff _ _)) in ND. destruct ND as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. rewrite map_app. apply in_app_iff. right. apply in_map. exact Hb. }
all: cbn [blk_addr blk_size fst snd] in D |- *; unfold SBSTATE_SIZEOF in D; lia. }

apply (RHEAP_perm _ _ (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB)) in HEAP_0; [| cbn [app]; apply Permutation_middle].
set (L0 := LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) in HEAP_0.
assert (INS0 : In (blk, S, SBSTATE_SIZEOF) L0) by (subst L0; apply in_app_iff; right; left; reflexivity).
assert (INL0 : forall b, In b LBL -> In b L0) by (intros b Hb; subst L0; apply in_app_iff; left; exact Hb).
assert (INB0 : forall b, In b LB -> In b L0) by (intros b Hb; subst L0; apply in_app_iff; right; right; exact Hb).
rewrite sb_init_rest_eq. change (QMF_ORDER * 4) with 256.
unfold sbx_cells in X_0. unfold sbinit_frame in FR_0.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e564) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 256) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_0 mq /\ wmono rsegs m_0 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_0) as MU. pose proof (wmono_refl rsegs m_0) as WM.
clear HEAP_0 PRES_0 RL_0. unfold sbx_cells in X_0.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_0 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_0 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_0 |- *.
all: step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX0" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX0" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq0 sfH_; first [ sf_destruct 19%nat sfH_ as mq0 xt00 xt10 xt20 xa20 xa30 xa40 xa50 xa60 xa70 xt30 xt40 xt50 xt60 -> Xq0 MUq0 WMq0 MIq0 | sf_fb; destruct sfH_ as (mq0 & xt00 & xt10 & xt20 & xa20 & xa30 & xa40 & xa50 & xa60 & xa70 & xt30 & xt40 & xt50 & xt60 & -> & Xq0 & MUq0 & WMq0 & MIq0) ].
assert (HEAPq0 : RHEAP st_0 L0 mq0).
{ eapply RHEAP_frame_proof; [exact HEAP_0| exact MUq0| exact WMq0|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS0| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq0 : rauxv_ok mq0 AB) by (eapply rauxv_ok_frame; [exact AUX_0| exact MUq0| exact WMq0| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq0 : rw_cells rsegs mq0 316332 [C4 errv_0]) by (eapply rw_cells_transport; [exact ERR_0| exact MUq0| exact WMq0| cbn; clear - SIMG; lia]).
assert (FRq0 : rw_cells rsegs mq0 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_0| exact MUq0| exact WMq0| cbn; clear - SLT SPR; lia]).
assert (STq0 : stk rsegs mq0 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_0| exact MUq0| exact WMq0| cbn; clear - SCE CLOv; lia]).
assert (TPq0 : rtables_pristine mq0) by (eapply rtables_pristine_munch; [exact TP_0| exact MUq0|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq0 : forall STEREO, DREP 0 STEREO mq0 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_0 STEREO)| exact MUq0| exact WMq0|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq0 : rheap_pres LB (bv_unsigned sp) m0 mq0).
{ eapply rheap_pres_trans; [exact PRES_0|]. eapply rheap_pres_of_munch; [exact MUq0| exact WMq0|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
clear X_0 HEAP_0 AUX_0 ERR_0 FR_0 ST_0 TP_0 RL_0 PRES_0 MUq0 WMq0 MI_0.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq0 st_0 L0 256 lo AB errv_0 HEAPq0 AUXq0);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq0| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq0| exact MIq0| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r0 st_1 msr0 sfH_; first [ sf_destruct 27%nat sfH_ as A0 y0_1 y1_1 y2_1 ya1_1 ya2_1 ya3_1 ya4_1 ya5_1 ya6_1 ya7_1 y3_1 y4_1 y5_1 y6_1 m_1 errv_1 -> MI_1 ST_1 ERR_1 AUX_1 HP_1 PSO_1 HEAP_1 ZR0 ZS0_1 | sf_fb; destruct sfH_ as (A0 & y0_1 & y1_1 & y2_1 & ya1_1 & ya2_1 & ya3_1 & ya4_1 & ya5_1 & ya6_1 & ya7_1 & y3_1 & y4_1 & y5_1 & y6_1 & m_1 & errv_1 & -> & MI_1 & ST_1 & ERR_1 & AUX_1 & HP_1 & PSO_1 & HEAP_1 & ZR0 & ZS0_1) ].
rewrite unsigned_lit in ST_1 by lia. rewrite unsigned_lit in HP_1 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_1. unfold RERRNO in ERR_1.
change (mem_inv rsegs m_1) in MI_1. change (stk rsegs m_1 lo (bv_unsigned sp + -48)) in ST_1. change (rw_cells rsegs m_1 316332 [C4 errv_1]) in ERR_1.
apply (RHEAP_perm _ _ (L0 ++ oblk r0 A0 256)) in HEAP_1; [| apply Permutation_app_comm].
set (L1 := L0 ++ oblk r0 A0 256) in HEAP_1.
assert (INS1 : In (blk, S, SBSTATE_SIZEOF) L1) by (subst L1; apply in_app_iff; left; exact INS0).
assert (INL1 : forall b, In b LBL -> In b L1) by (intros b Hb; subst L1; apply in_app_iff; left; apply INL0; exact Hb).
assert (INB1 : forall b, In b LB -> In b L1) by (intros b Hb; subst L1; apply in_app_iff; left; apply INB0; exact Hb).
assert (INr0 : forall p, r0 = Some p -> In (p, A0, 256) L1) by (intros p E; subst L1; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_1 := INr0).
assert (SA0 : forall p, r0 = Some p -> S + 160 <= A0 \/ A0 + 256 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_1) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A0, 256) (blk, S, SBSTATE_SIZEOF) HEAP_1 (INr0 p E) INS1) as [D|D].
{ subst L1. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L0 (blk, S, SBSTATE_SIZEOF)); exact INS0| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_1 : rw_cells rsegs m_1 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_1| exact Xq0|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS0| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_1 : rw_cells rsegs m_1 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_1| exact FRq0| left; cbn; lia]).
assert (TP_1 : rtables_pristine m_1) by (eapply rtables_pristine_rheap; [exact TPq0| exact HP_1]).
assert (RL_1 : forall STEREO, DREP 0 STEREO m_1 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq0 STEREO)| exact HP_1| exact INL0]).
assert (PRES_1 : rheap_pres LB (bv_unsigned sp) m0 m_1) by (eapply rheap_pres_trans; [exact PRESq0| eapply rheap_pres_weaken; [exact HP_1| lia| exact INB0]]).
assert (ZS_1_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_1 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS0_1 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
clear Xq0 HEAPq0 AUXq0 ERRq0 FRq0 STq0 TPq0 RLq0 PRESq0 HP_1 MIq0 ZS0_1.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e574) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 256) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_1 mq /\ wmono rsegs m_1 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_1) as MU. pose proof (wmono_refl rsegs m_1) as WM.
clear HEAP_1 PRES_1 RL_1. unfold sbx_cells in X_1.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_1 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_1 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_1 |- *.
all: lstep; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX1" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX1" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq1 sfH_; first [ sf_destruct 19%nat sfH_ as mq1 xt01 xt11 xt21 xa21 xa31 xa41 xa51 xa61 xa71 xt31 xt41 xt51 xt61 -> Xq1 MUq1 WMq1 MIq1 | sf_fb; destruct sfH_ as (mq1 & xt01 & xt11 & xt21 & xa21 & xa31 & xa41 & xa51 & xa61 & xa71 & xt31 & xt41 & xt51 & xt61 & -> & Xq1 & MUq1 & WMq1 & MIq1) ].
assert (HEAPq1 : RHEAP st_1 L1 mq1).
{ eapply RHEAP_frame_proof; [exact HEAP_1| exact MUq1| exact WMq1|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS1| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq1 : rauxv_ok mq1 AB) by (eapply rauxv_ok_frame; [exact AUX_1| exact MUq1| exact WMq1| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq1 : rw_cells rsegs mq1 316332 [C4 errv_1]) by (eapply rw_cells_transport; [exact ERR_1| exact MUq1| exact WMq1| cbn; clear - SIMG; lia]).
assert (FRq1 : rw_cells rsegs mq1 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_1| exact MUq1| exact WMq1| cbn; clear - SLT SPR; lia]).
assert (STq1 : stk rsegs mq1 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_1| exact MUq1| exact WMq1| cbn; clear - SCE CLOv; lia]).
assert (TPq1 : rtables_pristine mq1) by (eapply rtables_pristine_munch; [exact TP_1| exact MUq1|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq1 : forall STEREO, DREP 0 STEREO mq1 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_1 STEREO)| exact MUq1| exact WMq1|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq1 : rheap_pres LB (bv_unsigned sp) m0 mq1).
{ eapply rheap_pres_trans; [exact PRES_1|]. eapply rheap_pres_of_munch; [exact MUq1| exact WMq1|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq1_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq1 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_1_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq1| exact WMq1|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_1 HEAP_1 AUX_1 ERR_1 FR_1 ST_1 TP_1 RL_1 PRES_1 MUq1 WMq1 MI_1 ZS_1_0.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq1 st_1 L1 256 lo AB errv_1 HEAPq1 AUXq1);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq1| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq1| exact MIq1| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r1 st_2 msr1 sfH_; first [ sf_destruct 27%nat sfH_ as A1 y0_2 y1_2 y2_2 ya1_2 ya2_2 ya3_2 ya4_2 ya5_2 ya6_2 ya7_2 y3_2 y4_2 y5_2 y6_2 m_2 errv_2 -> MI_2 ST_2 ERR_2 AUX_2 HP_2 PSO_2 HEAP_2 ZR1 ZS0_2 | sf_fb; destruct sfH_ as (A1 & y0_2 & y1_2 & y2_2 & ya1_2 & ya2_2 & ya3_2 & ya4_2 & ya5_2 & ya6_2 & ya7_2 & y3_2 & y4_2 & y5_2 & y6_2 & m_2 & errv_2 & -> & MI_2 & ST_2 & ERR_2 & AUX_2 & HP_2 & PSO_2 & HEAP_2 & ZR1 & ZS0_2) ].
rewrite unsigned_lit in ST_2 by lia. rewrite unsigned_lit in HP_2 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_2. unfold RERRNO in ERR_2.
change (mem_inv rsegs m_2) in MI_2. change (stk rsegs m_2 lo (bv_unsigned sp + -48)) in ST_2. change (rw_cells rsegs m_2 316332 [C4 errv_2]) in ERR_2.
apply (RHEAP_perm _ _ (L1 ++ oblk r1 A1 256)) in HEAP_2; [| apply Permutation_app_comm].
set (L2 := L1 ++ oblk r1 A1 256) in HEAP_2.
assert (INS2 : In (blk, S, SBSTATE_SIZEOF) L2) by (subst L2; apply in_app_iff; left; exact INS1).
assert (INL2 : forall b, In b LBL -> In b L2) by (intros b Hb; subst L2; apply in_app_iff; left; apply INL1; exact Hb).
assert (INB2 : forall b, In b LB -> In b L2) by (intros b Hb; subst L2; apply in_app_iff; left; apply INB1; exact Hb).
assert (INr1 : forall p, r1 = Some p -> In (p, A1, 256) L2) by (intros p E; subst L2; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_2 : forall p, r0 = Some p -> In (p, A0, 256) L2) by (intros p E; subst L2; apply in_app_iff; left; exact (INr0_1 p E)).
assert (INr1_2 := INr1).
assert (SA1 : forall p, r1 = Some p -> S + 160 <= A1 \/ A1 + 256 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_2) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A1, 256) (blk, S, SBSTATE_SIZEOF) HEAP_2 (INr1 p E) INS2) as [D|D].
{ subst L2. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L1 (blk, S, SBSTATE_SIZEOF)); exact INS1| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_2 : rw_cells rsegs m_2 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_2| exact Xq1|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS1| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_2 : rw_cells rsegs m_2 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_2| exact FRq1| left; cbn; lia]).
assert (TP_2 : rtables_pristine m_2) by (eapply rtables_pristine_rheap; [exact TPq1| exact HP_2]).
assert (RL_2 : forall STEREO, DREP 0 STEREO m_2 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq1 STEREO)| exact HP_2| exact INL1]).
assert (PRES_2 : rheap_pres LB (bv_unsigned sp) m0 m_2) by (eapply rheap_pres_trans; [exact PRESq1| eapply rheap_pres_weaken; [exact HP_2| lia| exact INB1]]).
assert (ZS_2_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_2 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS0_2 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_2_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_2 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq1_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_2| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_1 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq1 HEAPq1 AUXq1 ERRq1 FRq1 STq1 TPq1 RLq1 PRESq1 HP_2 MIq1 ZS0_2 ZSq1_0.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e588) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 (sbm_subframeSize mo * 4)) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_2 mq /\ wmono rsegs m_2 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_2) as MU. pose proof (wmono_refl rsegs m_2) as WM.
clear HEAP_2 PRES_2 RL_2. unfold sbx_cells in X_2.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_2 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_2 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_2 |- *.
all: step; rewrite sx32_lit by lia; lstep; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX2" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX2" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq2 sfH_; first [ sf_destruct 19%nat sfH_ as mq2 xt02 xt12 xt22 xa22 xa32 xa42 xa52 xa62 xa72 xt32 xt42 xt52 xt62 -> Xq2 MUq2 WMq2 MIq2 | sf_fb; destruct sfH_ as (mq2 & xt02 & xt12 & xt22 & xa22 & xa32 & xa42 & xa52 & xa62 & xa72 & xt32 & xt42 & xt52 & xt62 & -> & Xq2 & MUq2 & WMq2 & MIq2) ].
assert (HEAPq2 : RHEAP st_2 L2 mq2).
{ eapply RHEAP_frame_proof; [exact HEAP_2| exact MUq2| exact WMq2|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS2| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq2 : rauxv_ok mq2 AB) by (eapply rauxv_ok_frame; [exact AUX_2| exact MUq2| exact WMq2| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq2 : rw_cells rsegs mq2 316332 [C4 errv_2]) by (eapply rw_cells_transport; [exact ERR_2| exact MUq2| exact WMq2| cbn; clear - SIMG; lia]).
assert (FRq2 : rw_cells rsegs mq2 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_2| exact MUq2| exact WMq2| cbn; clear - SLT SPR; lia]).
assert (STq2 : stk rsegs mq2 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_2| exact MUq2| exact WMq2| cbn; clear - SCE CLOv; lia]).
assert (TPq2 : rtables_pristine mq2) by (eapply rtables_pristine_munch; [exact TP_2| exact MUq2|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq2 : forall STEREO, DREP 0 STEREO mq2 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_2 STEREO)| exact MUq2| exact WMq2|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq2 : rheap_pres LB (bv_unsigned sp) m0 mq2).
{ eapply rheap_pres_trans; [exact PRES_2|]. eapply rheap_pres_of_munch; [exact MUq2| exact WMq2|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq2_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq2 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_2_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq2| exact WMq2|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq2_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq2 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_2_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq2| exact WMq2|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_2 HEAP_2 AUX_2 ERR_2 FR_2 ST_2 TP_2 RL_2 PRES_2 MUq2 WMq2 MI_2 ZS_2_0 ZS_2_1.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq2 st_2 L2 (sbm_subframeSize mo * 4) lo AB errv_2 HEAPq2 AUXq2);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq2| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq2| exact MIq2| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r2 st_3 msr2 sfH_; first [ sf_destruct 27%nat sfH_ as A2 y0_3 y1_3 y2_3 ya1_3 ya2_3 ya3_3 ya4_3 ya5_3 ya6_3 ya7_3 y3_3 y4_3 y5_3 y6_3 m_3 errv_3 -> MI_3 ST_3 ERR_3 AUX_3 HP_3 PSO_3 HEAP_3 ZR2 ZS0_3 | sf_fb; destruct sfH_ as (A2 & y0_3 & y1_3 & y2_3 & ya1_3 & ya2_3 & ya3_3 & ya4_3 & ya5_3 & ya6_3 & ya7_3 & y3_3 & y4_3 & y5_3 & y6_3 & m_3 & errv_3 & -> & MI_3 & ST_3 & ERR_3 & AUX_3 & HP_3 & PSO_3 & HEAP_3 & ZR2 & ZS0_3) ].
rewrite unsigned_lit in ST_3 by lia. rewrite unsigned_lit in HP_3 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_3. unfold RERRNO in ERR_3.
change (mem_inv rsegs m_3) in MI_3. change (stk rsegs m_3 lo (bv_unsigned sp + -48)) in ST_3. change (rw_cells rsegs m_3 316332 [C4 errv_3]) in ERR_3.
apply (RHEAP_perm _ _ (L2 ++ oblk r2 A2 (sbm_subframeSize mo * 4))) in HEAP_3; [| apply Permutation_app_comm].
set (L3 := L2 ++ oblk r2 A2 (sbm_subframeSize mo * 4)) in HEAP_3.
assert (INS3 : In (blk, S, SBSTATE_SIZEOF) L3) by (subst L3; apply in_app_iff; left; exact INS2).
assert (INL3 : forall b, In b LBL -> In b L3) by (intros b Hb; subst L3; apply in_app_iff; left; apply INL2; exact Hb).
assert (INB3 : forall b, In b LB -> In b L3) by (intros b Hb; subst L3; apply in_app_iff; left; apply INB2; exact Hb).
assert (INr2 : forall p, r2 = Some p -> In (p, A2, (sbm_subframeSize mo * 4)) L3) by (intros p E; subst L3; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_3 : forall p, r0 = Some p -> In (p, A0, 256) L3) by (intros p E; subst L3; apply in_app_iff; left; exact (INr0_2 p E)).
assert (INr1_3 : forall p, r1 = Some p -> In (p, A1, 256) L3) by (intros p E; subst L3; apply in_app_iff; left; exact (INr1_2 p E)).
assert (INr2_3 := INr2).
assert (SA2 : forall p, r2 = Some p -> S + 160 <= A2 \/ A2 + (sbm_subframeSize mo * 4) <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_3) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A2, (sbm_subframeSize mo * 4)) (blk, S, SBSTATE_SIZEOF) HEAP_3 (INr2 p E) INS3) as [D|D].
{ subst L3. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L2 (blk, S, SBSTATE_SIZEOF)); exact INS2| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_3 : rw_cells rsegs m_3 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_3| exact Xq2|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS2| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_3 : rw_cells rsegs m_3 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_3| exact FRq2| left; cbn; lia]).
assert (TP_3 : rtables_pristine m_3) by (eapply rtables_pristine_rheap; [exact TPq2| exact HP_3]).
assert (RL_3 : forall STEREO, DREP 0 STEREO m_3 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq2 STEREO)| exact HP_3| exact INL2]).
assert (PRES_3 : rheap_pres LB (bv_unsigned sp) m0 m_3) by (eapply rheap_pres_trans; [exact PRESq2| eapply rheap_pres_weaken; [exact HP_3| lia| exact INB2]]).
assert (ZS_3_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs m_3 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS0_3 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_3_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_3 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq2_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_3| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_2 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_3_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_3 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq2_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_3| exact Zj|]. right; right. exists (p, A1, 256).
split; [exact (INr1_2 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq2 HEAPq2 AUXq2 ERRq2 FRq2 STq2 TPq2 RLq2 PRESq2 HP_3 MIq2 ZS0_3 ZSq2_0 ZSq2_1.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e59c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 (sbm_lpcSize mo * 4)) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_3 mq /\ wmono rsegs m_3 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_3) as MU. pose proof (wmono_refl rsegs m_3) as WM.
clear HEAP_3 PRES_3 RL_3. unfold sbx_cells in X_3.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_3 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_3 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_3 |- *.
all: step; rewrite sx32_lit by lia; lstep; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX3" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX3" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq3 sfH_; first [ sf_destruct 19%nat sfH_ as mq3 xt03 xt13 xt23 xa23 xa33 xa43 xa53 xa63 xa73 xt33 xt43 xt53 xt63 -> Xq3 MUq3 WMq3 MIq3 | sf_fb; destruct sfH_ as (mq3 & xt03 & xt13 & xt23 & xa23 & xa33 & xa43 & xa53 & xa63 & xa73 & xt33 & xt43 & xt53 & xt63 & -> & Xq3 & MUq3 & WMq3 & MIq3) ].
assert (HEAPq3 : RHEAP st_3 L3 mq3).
{ eapply RHEAP_frame_proof; [exact HEAP_3| exact MUq3| exact WMq3|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS3| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq3 : rauxv_ok mq3 AB) by (eapply rauxv_ok_frame; [exact AUX_3| exact MUq3| exact WMq3| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq3 : rw_cells rsegs mq3 316332 [C4 errv_3]) by (eapply rw_cells_transport; [exact ERR_3| exact MUq3| exact WMq3| cbn; clear - SIMG; lia]).
assert (FRq3 : rw_cells rsegs mq3 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_3| exact MUq3| exact WMq3| cbn; clear - SLT SPR; lia]).
assert (STq3 : stk rsegs mq3 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_3| exact MUq3| exact WMq3| cbn; clear - SCE CLOv; lia]).
assert (TPq3 : rtables_pristine mq3) by (eapply rtables_pristine_munch; [exact TP_3| exact MUq3|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq3 : forall STEREO, DREP 0 STEREO mq3 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_3 STEREO)| exact MUq3| exact WMq3|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq3 : rheap_pres LB (bv_unsigned sp) m0 mq3).
{ eapply rheap_pres_trans; [exact PRES_3|]. eapply rheap_pres_of_munch; [exact MUq3| exact WMq3|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq3_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq3 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_3_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq3| exact WMq3|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq3_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq3 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_3_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq3| exact WMq3|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq3_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs mq3 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS_3_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq3| exact WMq3|].
destruct (SA2 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_3 HEAP_3 AUX_3 ERR_3 FR_3 ST_3 TP_3 RL_3 PRES_3 MUq3 WMq3 MI_3 ZS_3_0 ZS_3_1 ZS_3_2.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq3 st_3 L3 (sbm_lpcSize mo * 4) lo AB errv_3 HEAPq3 AUXq3);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq3| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq3| exact MIq3| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r3 st_4 msr3 sfH_; first [ sf_destruct 27%nat sfH_ as A3 y0_4 y1_4 y2_4 ya1_4 ya2_4 ya3_4 ya4_4 ya5_4 ya6_4 ya7_4 y3_4 y4_4 y5_4 y6_4 m_4 errv_4 -> MI_4 ST_4 ERR_4 AUX_4 HP_4 PSO_4 HEAP_4 ZR3 ZS0_4 | sf_fb; destruct sfH_ as (A3 & y0_4 & y1_4 & y2_4 & ya1_4 & ya2_4 & ya3_4 & ya4_4 & ya5_4 & ya6_4 & ya7_4 & y3_4 & y4_4 & y5_4 & y6_4 & m_4 & errv_4 & -> & MI_4 & ST_4 & ERR_4 & AUX_4 & HP_4 & PSO_4 & HEAP_4 & ZR3 & ZS0_4) ].
rewrite unsigned_lit in ST_4 by lia. rewrite unsigned_lit in HP_4 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_4. unfold RERRNO in ERR_4.
change (mem_inv rsegs m_4) in MI_4. change (stk rsegs m_4 lo (bv_unsigned sp + -48)) in ST_4. change (rw_cells rsegs m_4 316332 [C4 errv_4]) in ERR_4.
apply (RHEAP_perm _ _ (L3 ++ oblk r3 A3 (sbm_lpcSize mo * 4))) in HEAP_4; [| apply Permutation_app_comm].
set (L4 := L3 ++ oblk r3 A3 (sbm_lpcSize mo * 4)) in HEAP_4.
assert (INS4 : In (blk, S, SBSTATE_SIZEOF) L4) by (subst L4; apply in_app_iff; left; exact INS3).
assert (INL4 : forall b, In b LBL -> In b L4) by (intros b Hb; subst L4; apply in_app_iff; left; apply INL3; exact Hb).
assert (INB4 : forall b, In b LB -> In b L4) by (intros b Hb; subst L4; apply in_app_iff; left; apply INB3; exact Hb).
assert (INr3 : forall p, r3 = Some p -> In (p, A3, (sbm_lpcSize mo * 4)) L4) by (intros p E; subst L4; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_4 : forall p, r0 = Some p -> In (p, A0, 256) L4) by (intros p E; subst L4; apply in_app_iff; left; exact (INr0_3 p E)).
assert (INr1_4 : forall p, r1 = Some p -> In (p, A1, 256) L4) by (intros p E; subst L4; apply in_app_iff; left; exact (INr1_3 p E)).
assert (INr2_4 : forall p, r2 = Some p -> In (p, A2, (sbm_subframeSize mo * 4)) L4) by (intros p E; subst L4; apply in_app_iff; left; exact (INr2_3 p E)).
assert (INr3_4 := INr3).
assert (SA3 : forall p, r3 = Some p -> S + 160 <= A3 \/ A3 + 32 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_4) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A3, (sbm_lpcSize mo * 4)) (blk, S, SBSTATE_SIZEOF) HEAP_4 (INr3 p E) INS4) as [D|D].
{ subst L4. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L3 (blk, S, SBSTATE_SIZEOF)); exact INS3| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_4 : rw_cells rsegs m_4 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_4| exact Xq3|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS3| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_4 : rw_cells rsegs m_4 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_4| exact FRq3| left; cbn; lia]).
assert (TP_4 : rtables_pristine m_4) by (eapply rtables_pristine_rheap; [exact TPq3| exact HP_4]).
assert (RL_4 : forall STEREO, DREP 0 STEREO m_4 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq3 STEREO)| exact HP_4| exact INL3]).
assert (PRES_4 : rheap_pres LB (bv_unsigned sp) m0 m_4) by (eapply rheap_pres_trans; [exact PRESq3| eapply rheap_pres_weaken; [exact HP_4| lia| exact INB3]]).
assert (ZS_4_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs m_4 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS0_4 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_4_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_4 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq3_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_4| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_3 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_4_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_4 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq3_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_4| exact Zj|]. right; right. exists (p, A1, 256).
split; [exact (INr1_3 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_4_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs m_4 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZSq3_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_4| exact Zj|]. right; right. exists (p, A2, (sbm_subframeSize mo * 4)).
split; [exact (INr2_3 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq3 HEAPq3 AUXq3 ERRq3 FRq3 STq3 TPq3 RLq3 PRESq3 HP_4 MIq3 ZS0_4 ZSq3_0 ZSq3_1 ZSq3_2.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e5b0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 (sbm_lpcSize mo * 4)) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_4 mq /\ wmono rsegs m_4 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_4) as MU. pose proof (wmono_refl rsegs m_4) as WM.
clear HEAP_4 PRES_4 RL_4. unfold sbx_cells in X_4.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_4 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_4 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_4 |- *.
all: step; rewrite sx32_lit by lia; lstep; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX4" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX4" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq4 sfH_; first [ sf_destruct 19%nat sfH_ as mq4 xt04 xt14 xt24 xa24 xa34 xa44 xa54 xa64 xa74 xt34 xt44 xt54 xt64 -> Xq4 MUq4 WMq4 MIq4 | sf_fb; destruct sfH_ as (mq4 & xt04 & xt14 & xt24 & xa24 & xa34 & xa44 & xa54 & xa64 & xa74 & xt34 & xt44 & xt54 & xt64 & -> & Xq4 & MUq4 & WMq4 & MIq4) ].
assert (HEAPq4 : RHEAP st_4 L4 mq4).
{ eapply RHEAP_frame_proof; [exact HEAP_4| exact MUq4| exact WMq4|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS4| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq4 : rauxv_ok mq4 AB) by (eapply rauxv_ok_frame; [exact AUX_4| exact MUq4| exact WMq4| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq4 : rw_cells rsegs mq4 316332 [C4 errv_4]) by (eapply rw_cells_transport; [exact ERR_4| exact MUq4| exact WMq4| cbn; clear - SIMG; lia]).
assert (FRq4 : rw_cells rsegs mq4 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_4| exact MUq4| exact WMq4| cbn; clear - SLT SPR; lia]).
assert (STq4 : stk rsegs mq4 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_4| exact MUq4| exact WMq4| cbn; clear - SCE CLOv; lia]).
assert (TPq4 : rtables_pristine mq4) by (eapply rtables_pristine_munch; [exact TP_4| exact MUq4|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq4 : forall STEREO, DREP 0 STEREO mq4 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_4 STEREO)| exact MUq4| exact WMq4|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq4 : rheap_pres LB (bv_unsigned sp) m0 mq4).
{ eapply rheap_pres_trans; [exact PRES_4|]. eapply rheap_pres_of_munch; [exact MUq4| exact WMq4|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq4_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq4 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_4_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq4| exact WMq4|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq4_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq4 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_4_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq4| exact WMq4|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq4_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs mq4 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS_4_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq4| exact WMq4|].
destruct (SA2 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq4_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs mq4 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_4_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq4| exact WMq4|].
destruct (SA3 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_4 HEAP_4 AUX_4 ERR_4 FR_4 ST_4 TP_4 RL_4 PRES_4 MUq4 WMq4 MI_4 ZS_4_0 ZS_4_1 ZS_4_2 ZS_4_3.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq4 st_4 L4 (sbm_lpcSize mo * 4) lo AB errv_4 HEAPq4 AUXq4);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq4| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq4| exact MIq4| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r4 st_5 msr4 sfH_; first [ sf_destruct 27%nat sfH_ as A4 y0_5 y1_5 y2_5 ya1_5 ya2_5 ya3_5 ya4_5 ya5_5 ya6_5 ya7_5 y3_5 y4_5 y5_5 y6_5 m_5 errv_5 -> MI_5 ST_5 ERR_5 AUX_5 HP_5 PSO_5 HEAP_5 ZR4 ZS0_5 | sf_fb; destruct sfH_ as (A4 & y0_5 & y1_5 & y2_5 & ya1_5 & ya2_5 & ya3_5 & ya4_5 & ya5_5 & ya6_5 & ya7_5 & y3_5 & y4_5 & y5_5 & y6_5 & m_5 & errv_5 & -> & MI_5 & ST_5 & ERR_5 & AUX_5 & HP_5 & PSO_5 & HEAP_5 & ZR4 & ZS0_5) ].
rewrite unsigned_lit in ST_5 by lia. rewrite unsigned_lit in HP_5 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_5. unfold RERRNO in ERR_5.
change (mem_inv rsegs m_5) in MI_5. change (stk rsegs m_5 lo (bv_unsigned sp + -48)) in ST_5. change (rw_cells rsegs m_5 316332 [C4 errv_5]) in ERR_5.
apply (RHEAP_perm _ _ (L4 ++ oblk r4 A4 (sbm_lpcSize mo * 4))) in HEAP_5; [| apply Permutation_app_comm].
set (L5 := L4 ++ oblk r4 A4 (sbm_lpcSize mo * 4)) in HEAP_5.
assert (INS5 : In (blk, S, SBSTATE_SIZEOF) L5) by (subst L5; apply in_app_iff; left; exact INS4).
assert (INL5 : forall b, In b LBL -> In b L5) by (intros b Hb; subst L5; apply in_app_iff; left; apply INL4; exact Hb).
assert (INB5 : forall b, In b LB -> In b L5) by (intros b Hb; subst L5; apply in_app_iff; left; apply INB4; exact Hb).
assert (INr4 : forall p, r4 = Some p -> In (p, A4, (sbm_lpcSize mo * 4)) L5) by (intros p E; subst L5; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_5 : forall p, r0 = Some p -> In (p, A0, 256) L5) by (intros p E; subst L5; apply in_app_iff; left; exact (INr0_4 p E)).
assert (INr1_5 : forall p, r1 = Some p -> In (p, A1, 256) L5) by (intros p E; subst L5; apply in_app_iff; left; exact (INr1_4 p E)).
assert (INr2_5 : forall p, r2 = Some p -> In (p, A2, (sbm_subframeSize mo * 4)) L5) by (intros p E; subst L5; apply in_app_iff; left; exact (INr2_4 p E)).
assert (INr3_5 : forall p, r3 = Some p -> In (p, A3, (sbm_lpcSize mo * 4)) L5) by (intros p E; subst L5; apply in_app_iff; left; exact (INr3_4 p E)).
assert (INr4_5 := INr4).
assert (SA4 : forall p, r4 = Some p -> S + 160 <= A4 \/ A4 + 32 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_5) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A4, (sbm_lpcSize mo * 4)) (blk, S, SBSTATE_SIZEOF) HEAP_5 (INr4 p E) INS5) as [D|D].
{ subst L5. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L4 (blk, S, SBSTATE_SIZEOF)); exact INS4| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_5 : rw_cells rsegs m_5 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_5| exact Xq4|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS4| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_5 : rw_cells rsegs m_5 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_5| exact FRq4| left; cbn; lia]).
assert (TP_5 : rtables_pristine m_5) by (eapply rtables_pristine_rheap; [exact TPq4| exact HP_5]).
assert (RL_5 : forall STEREO, DREP 0 STEREO m_5 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq4 STEREO)| exact HP_5| exact INL4]).
assert (PRES_5 : rheap_pres LB (bv_unsigned sp) m0 m_5) by (eapply rheap_pres_trans; [exact PRESq4| eapply rheap_pres_weaken; [exact HP_5| lia| exact INB4]]).
assert (ZS_5_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs m_5 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS0_5 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_5_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_5 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq4_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_5| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_4 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_5_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_5 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq4_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_5| exact Zj|]. right; right. exists (p, A1, 256).
split; [exact (INr1_4 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_5_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs m_5 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZSq4_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_5| exact Zj|]. right; right. exists (p, A2, (sbm_subframeSize mo * 4)).
split; [exact (INr2_4 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_5_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs m_5 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq4_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_5| exact Zj|]. right; right. exists (p, A3, (sbm_lpcSize mo * 4)).
split; [exact (INr3_4 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq4 HEAPq4 AUXq4 ERRq4 FRq4 STq4 TPq4 RLq4 PRESq4 HP_5 MIq4 ZS0_5 ZSq4_0 ZSq4_1 ZSq4_2 ZSq4_3.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e5c4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_5 mq /\ wmono rsegs m_5 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_5) as MU. pose proof (wmono_refl rsegs m_5) as WM.
clear HEAP_5 PRES_5 RL_5. unfold sbx_cells in X_5.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_5 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_5 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_5 |- *.
all: step; rewrite sx32_lit by lia; lstep; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX5" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX5" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq5 sfH_; first [ sf_destruct 19%nat sfH_ as mq5 xt05 xt15 xt25 xa25 xa35 xa45 xa55 xa65 xa75 xt35 xt45 xt55 xt65 -> Xq5 MUq5 WMq5 MIq5 | sf_fb; destruct sfH_ as (mq5 & xt05 & xt15 & xt25 & xa25 & xa35 & xa45 & xa55 & xa65 & xa75 & xt35 & xt45 & xt55 & xt65 & -> & Xq5 & MUq5 & WMq5 & MIq5) ].
assert (HEAPq5 : RHEAP st_5 L5 mq5).
{ eapply RHEAP_frame_proof; [exact HEAP_5| exact MUq5| exact WMq5|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS5| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq5 : rauxv_ok mq5 AB) by (eapply rauxv_ok_frame; [exact AUX_5| exact MUq5| exact WMq5| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq5 : rw_cells rsegs mq5 316332 [C4 errv_5]) by (eapply rw_cells_transport; [exact ERR_5| exact MUq5| exact WMq5| cbn; clear - SIMG; lia]).
assert (FRq5 : rw_cells rsegs mq5 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_5| exact MUq5| exact WMq5| cbn; clear - SLT SPR; lia]).
assert (STq5 : stk rsegs mq5 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_5| exact MUq5| exact WMq5| cbn; clear - SCE CLOv; lia]).
assert (TPq5 : rtables_pristine mq5) by (eapply rtables_pristine_munch; [exact TP_5| exact MUq5|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq5 : forall STEREO, DREP 0 STEREO mq5 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_5 STEREO)| exact MUq5| exact WMq5|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq5 : rheap_pres LB (bv_unsigned sp) m0 mq5).
{ eapply rheap_pres_trans; [exact PRES_5|]. eapply rheap_pres_of_munch; [exact MUq5| exact WMq5|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq5_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq5 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_5_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq5| exact WMq5|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq5_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq5 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_5_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq5| exact WMq5|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq5_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs mq5 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS_5_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq5| exact WMq5|].
destruct (SA2 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq5_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs mq5 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_5_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq5| exact WMq5|].
destruct (SA3 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq5_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs mq5 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_5_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq5| exact WMq5|].
destruct (SA4 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_5 HEAP_5 AUX_5 ERR_5 FR_5 ST_5 TP_5 RL_5 PRES_5 MUq5 WMq5 MI_5 ZS_5_0 ZS_5_1 ZS_5_2 ZS_5_3 ZS_5_4.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq5 st_5 L5 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) lo AB errv_5 HEAPq5 AUXq5);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq5| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq5| exact MIq5| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r5 st_6 msr5 sfH_; first [ sf_destruct 27%nat sfH_ as A5 y0_6 y1_6 y2_6 ya1_6 ya2_6 ya3_6 ya4_6 ya5_6 ya6_6 ya7_6 y3_6 y4_6 y5_6 y6_6 m_6 errv_6 -> MI_6 ST_6 ERR_6 AUX_6 HP_6 PSO_6 HEAP_6 ZR5 ZS0_6 | sf_fb; destruct sfH_ as (A5 & y0_6 & y1_6 & y2_6 & ya1_6 & ya2_6 & ya3_6 & ya4_6 & ya5_6 & ya6_6 & ya7_6 & y3_6 & y4_6 & y5_6 & y6_6 & m_6 & errv_6 & -> & MI_6 & ST_6 & ERR_6 & AUX_6 & HP_6 & PSO_6 & HEAP_6 & ZR5 & ZS0_6) ].
rewrite unsigned_lit in ST_6 by lia. rewrite unsigned_lit in HP_6 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_6. unfold RERRNO in ERR_6.
change (mem_inv rsegs m_6) in MI_6. change (stk rsegs m_6 lo (bv_unsigned sp + -48)) in ST_6. change (rw_cells rsegs m_6 316332 [C4 errv_6]) in ERR_6.
apply (RHEAP_perm _ _ (L5 ++ oblk r5 A5 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4))) in HEAP_6; [| apply Permutation_app_comm].
set (L6 := L5 ++ oblk r5 A5 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) in HEAP_6.
assert (INS6 : In (blk, S, SBSTATE_SIZEOF) L6) by (subst L6; apply in_app_iff; left; exact INS5).
assert (INL6 : forall b, In b LBL -> In b L6) by (intros b Hb; subst L6; apply in_app_iff; left; apply INL5; exact Hb).
assert (INB6 : forall b, In b LB -> In b L6) by (intros b Hb; subst L6; apply in_app_iff; left; apply INB5; exact Hb).
assert (INr5 : forall p, r5 = Some p -> In (p, A5, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) L6) by (intros p E; subst L6; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_6 : forall p, r0 = Some p -> In (p, A0, 256) L6) by (intros p E; subst L6; apply in_app_iff; left; exact (INr0_5 p E)).
assert (INr1_6 : forall p, r1 = Some p -> In (p, A1, 256) L6) by (intros p E; subst L6; apply in_app_iff; left; exact (INr1_5 p E)).
assert (INr2_6 : forall p, r2 = Some p -> In (p, A2, (sbm_subframeSize mo * 4)) L6) by (intros p E; subst L6; apply in_app_iff; left; exact (INr2_5 p E)).
assert (INr3_6 : forall p, r3 = Some p -> In (p, A3, (sbm_lpcSize mo * 4)) L6) by (intros p E; subst L6; apply in_app_iff; left; exact (INr3_5 p E)).
assert (INr4_6 : forall p, r4 = Some p -> In (p, A4, (sbm_lpcSize mo * 4)) L6) by (intros p E; subst L6; apply in_app_iff; left; exact (INr4_5 p E)).
assert (INr5_6 := INr5).
assert (SA5 : forall p, r5 = Some p -> S + 160 <= A5 \/ A5 + 16 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_6) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A5, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) (blk, S, SBSTATE_SIZEOF) HEAP_6 (INr5 p E) INS6) as [D|D].
{ subst L6. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L5 (blk, S, SBSTATE_SIZEOF)); exact INS5| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_6 : rw_cells rsegs m_6 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 0 0 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_6| exact Xq5|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS5| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_6 : rw_cells rsegs m_6 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_6| exact FRq5| left; cbn; lia]).
assert (TP_6 : rtables_pristine m_6) by (eapply rtables_pristine_rheap; [exact TPq5| exact HP_6]).
assert (RL_6 : forall STEREO, DREP 0 STEREO m_6 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq5 STEREO)| exact HP_6| exact INL5]).
assert (PRES_6 : rheap_pres LB (bv_unsigned sp) m0 m_6) by (eapply rheap_pres_trans; [exact PRESq5| eapply rheap_pres_weaken; [exact HP_6| lia| exact INB5]]).
assert (ZS_6_5 : forall p, r5 = Some p -> rblock_range A5 16 /\ rw_cells rsegs m_6 A5 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS0_6 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_6_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_6 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq5_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_6| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_5 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_6_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_6 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq5_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_6| exact Zj|]. right; right. exists (p, A1, 256).
split; [exact (INr1_5 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_6_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs m_6 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZSq5_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_6| exact Zj|]. right; right. exists (p, A2, (sbm_subframeSize mo * 4)).
split; [exact (INr2_5 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_6_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs m_6 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq5_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_6| exact Zj|]. right; right. exists (p, A3, (sbm_lpcSize mo * 4)).
split; [exact (INr3_5 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_6_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs m_6 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq5_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_6| exact Zj|]. right; right. exists (p, A4, (sbm_lpcSize mo * 4)).
split; [exact (INr4_5 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq5 HEAPq5 AUXq5 ERRq5 FRq5 STq5 TPq5 RLq5 PRESq5 HP_6 MIq5 ZS0_6 ZSq5_0 ZSq5_1 ZSq5_2 ZSq5_3 ZSq5_4.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e5d8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824)
(Z_to_bv 64 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 0 A5 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_6 mq /\ wmono rsegs m_6 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_6) as MU. pose proof (wmono_refl rsegs m_6) as WM.
clear HEAP_6 PRES_6 RL_6. unfold sbx_cells in X_6.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_6 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_6 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_6 |- *.
all: step; rewrite sx32_lit by lia; lstep; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX6" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX6" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq6 sfH_; first [ sf_destruct 19%nat sfH_ as mq6 xt06 xt16 xt26 xa26 xa36 xa46 xa56 xa66 xa76 xt36 xt46 xt56 xt66 -> Xq6 MUq6 WMq6 MIq6 | sf_fb; destruct sfH_ as (mq6 & xt06 & xt16 & xt26 & xa26 & xa36 & xa46 & xa56 & xa66 & xa76 & xt36 & xt46 & xt56 & xt66 & -> & Xq6 & MUq6 & WMq6 & MIq6) ].
assert (HEAPq6 : RHEAP st_6 L6 mq6).
{ eapply RHEAP_frame_proof; [exact HEAP_6| exact MUq6| exact WMq6|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS6| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq6 : rauxv_ok mq6 AB) by (eapply rauxv_ok_frame; [exact AUX_6| exact MUq6| exact WMq6| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq6 : rw_cells rsegs mq6 316332 [C4 errv_6]) by (eapply rw_cells_transport; [exact ERR_6| exact MUq6| exact WMq6| cbn; clear - SIMG; lia]).
assert (FRq6 : rw_cells rsegs mq6 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_6| exact MUq6| exact WMq6| cbn; clear - SLT SPR; lia]).
assert (STq6 : stk rsegs mq6 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_6| exact MUq6| exact WMq6| cbn; clear - SCE CLOv; lia]).
assert (TPq6 : rtables_pristine mq6) by (eapply rtables_pristine_munch; [exact TP_6| exact MUq6|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq6 : forall STEREO, DREP 0 STEREO mq6 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_6 STEREO)| exact MUq6| exact WMq6|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq6 : rheap_pres LB (bv_unsigned sp) m0 mq6).
{ eapply rheap_pres_trans; [exact PRES_6|]. eapply rheap_pres_of_munch; [exact MUq6| exact WMq6|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq6_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq6 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_6_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq6| exact WMq6|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq6_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq6 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_6_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq6| exact WMq6|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq6_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs mq6 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS_6_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq6| exact WMq6|].
destruct (SA2 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq6_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs mq6 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_6_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq6| exact WMq6|].
destruct (SA3 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq6_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs mq6 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_6_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq6| exact WMq6|].
destruct (SA4 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq6_5 : forall p, r5 = Some p -> rblock_range A5 16 /\ rw_cells rsegs mq6 A5 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS_6_5 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq6| exact WMq6|].
destruct (SA5 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_6 HEAP_6 AUX_6 ERR_6 FR_6 ST_6 TP_6 RL_6 PRES_6 MUq6 WMq6 MI_6 ZS_6_0 ZS_6_1 ZS_6_2 ZS_6_3 ZS_6_4 ZS_6_5.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq6 st_6 L6 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) lo AB errv_6 HEAPq6 AUXq6);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq6| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq6| exact MIq6| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r6 st_7 msr6 sfH_; first [ sf_destruct 27%nat sfH_ as A6 y0_7 y1_7 y2_7 ya1_7 ya2_7 ya3_7 ya4_7 ya5_7 ya6_7 ya7_7 y3_7 y4_7 y5_7 y6_7 m_7 errv_7 -> MI_7 ST_7 ERR_7 AUX_7 HP_7 PSO_7 HEAP_7 ZR6 ZS0_7 | sf_fb; destruct sfH_ as (A6 & y0_7 & y1_7 & y2_7 & ya1_7 & ya2_7 & ya3_7 & ya4_7 & ya5_7 & ya6_7 & ya7_7 & y3_7 & y4_7 & y5_7 & y6_7 & m_7 & errv_7 & -> & MI_7 & ST_7 & ERR_7 & AUX_7 & HP_7 & PSO_7 & HEAP_7 & ZR6 & ZS0_7) ].
rewrite unsigned_lit in ST_7 by lia. rewrite unsigned_lit in HP_7 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_7. unfold RERRNO in ERR_7.
change (mem_inv rsegs m_7) in MI_7. change (stk rsegs m_7 lo (bv_unsigned sp + -48)) in ST_7. change (rw_cells rsegs m_7 316332 [C4 errv_7]) in ERR_7.
apply (RHEAP_perm _ _ (L6 ++ oblk r6 A6 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4))) in HEAP_7; [| apply Permutation_app_comm].
set (L7 := L6 ++ oblk r6 A6 (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) in HEAP_7.
assert (INS7 : In (blk, S, SBSTATE_SIZEOF) L7) by (subst L7; apply in_app_iff; left; exact INS6).
assert (INL7 : forall b, In b LBL -> In b L7) by (intros b Hb; subst L7; apply in_app_iff; left; apply INL6; exact Hb).
assert (INB7 : forall b, In b LB -> In b L7) by (intros b Hb; subst L7; apply in_app_iff; left; apply INB6; exact Hb).
assert (INr6 : forall p, r6 = Some p -> In (p, A6, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) L7) by (intros p E; subst L7; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_7 : forall p, r0 = Some p -> In (p, A0, 256) L7) by (intros p E; subst L7; apply in_app_iff; left; exact (INr0_6 p E)).
assert (INr1_7 : forall p, r1 = Some p -> In (p, A1, 256) L7) by (intros p E; subst L7; apply in_app_iff; left; exact (INr1_6 p E)).
assert (INr2_7 : forall p, r2 = Some p -> In (p, A2, (sbm_subframeSize mo * 4)) L7) by (intros p E; subst L7; apply in_app_iff; left; exact (INr2_6 p E)).
assert (INr3_7 : forall p, r3 = Some p -> In (p, A3, (sbm_lpcSize mo * 4)) L7) by (intros p E; subst L7; apply in_app_iff; left; exact (INr3_6 p E)).
assert (INr4_7 : forall p, r4 = Some p -> In (p, A4, (sbm_lpcSize mo * 4)) L7) by (intros p E; subst L7; apply in_app_iff; left; exact (INr4_6 p E)).
assert (INr5_7 : forall p, r5 = Some p -> In (p, A5, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) L7) by (intros p E; subst L7; apply in_app_iff; left; exact (INr5_6 p E)).
assert (INr6_7 := INr6).
assert (SA6 : forall p, r6 = Some p -> S + 160 <= A6 \/ A6 + 16 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_7) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A6, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) (blk, S, SBSTATE_SIZEOF) HEAP_7 (INr6 p E) INS7) as [D|D].
{ subst L7. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L6 (blk, S, SBSTATE_SIZEOF)); exact INS6| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_7 : rw_cells rsegs m_7 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 0 A5 0 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_7| exact Xq6|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS6| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_7 : rw_cells rsegs m_7 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_7| exact FRq6| left; cbn; lia]).
assert (TP_7 : rtables_pristine m_7) by (eapply rtables_pristine_rheap; [exact TPq6| exact HP_7]).
assert (RL_7 : forall STEREO, DREP 0 STEREO m_7 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq6 STEREO)| exact HP_7| exact INL6]).
assert (PRES_7 : rheap_pres LB (bv_unsigned sp) m0 m_7) by (eapply rheap_pres_trans; [exact PRESq6| eapply rheap_pres_weaken; [exact HP_7| lia| exact INB6]]).
assert (ZS_7_6 : forall p, r6 = Some p -> rblock_range A6 16 /\ rw_cells rsegs m_7 A6 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS0_7 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_7_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_7 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq6_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_7| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_6 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_7_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_7 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq6_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_7| exact Zj|]. right; right. exists (p, A1, 256).
split; [exact (INr1_6 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_7_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs m_7 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZSq6_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_7| exact Zj|]. right; right. exists (p, A2, (sbm_subframeSize mo * 4)).
split; [exact (INr2_6 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_7_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs m_7 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq6_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_7| exact Zj|]. right; right. exists (p, A3, (sbm_lpcSize mo * 4)).
split; [exact (INr3_6 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_7_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs m_7 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq6_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_7| exact Zj|]. right; right. exists (p, A4, (sbm_lpcSize mo * 4)).
split; [exact (INr4_6 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_7_5 : forall p, r5 = Some p -> rblock_range A5 16 /\ rw_cells rsegs m_7 A5 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZSq6_5 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_7| exact Zj|]. right; right. exists (p, A5, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)).
split; [exact (INr5_6 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq6 HEAPq6 AUXq6 ERRq6 FRq6 STq6 TPq6 RLq6 PRESq6 HP_7 MIq6 ZS0_7 ZSq6_0 ZSq6_1 ZSq6_2 ZSq6_3 ZSq6_4 ZSq6_5.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
msq = MS (mkR (Z_to_bv 64 0x2e5f4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 (sbm_lpcSize mo + 1073741824))
(Z_to_bv 64 (2 * sbm_lpcSize mo * 4)) (Z_to_bv 64 1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F0 (Z_to_bv 64 RCALLOC_SYM) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 0 A5 A6 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_7 mq /\ wmono rsegs m_7 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_7) as MU. pose proof (wmono_refl rsegs m_7) as WM.
clear HEAP_7 PRES_7 RL_7. unfold sbx_cells in X_7.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr sbm_frameSize sbm_subframeSize sbm_lpcSize sbm_defaultSubmode] in X_7 |- *;
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in X_7 |- *; cbn [Z.mul Pos.mul Z.quot Z.quotrem N.pos_div_eucl Z.of_N fst Pos.add Z.add] in X_7 |- *.
all: step; rewrite sx32_lit by lia; step; lstep; step; if_false_x; step; step; step.
all: apply evt_done; sf_eexists 14%nat; (split; [first [reflexivity | match goal with |- ?g => idtac "REGFIX7" g end; fail 1]|]);
(split; [unfold sbx_cells; first [eassumption | match goal with |- ?g => idtac "XFIX7" g end; fail 1]|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq7 sfH_; first [ sf_destruct 19%nat sfH_ as mq7 xt07 xt17 xt27 xa27 xa37 xa47 xa57 xa67 xa77 xt37 xt47 xt57 xt67 -> Xq7 MUq7 WMq7 MIq7 | sf_fb; destruct sfH_ as (mq7 & xt07 & xt17 & xt27 & xa27 & xa37 & xa47 & xa57 & xa67 & xa77 & xt37 & xt47 & xt57 & xt67 & -> & Xq7 & MUq7 & WMq7 & MIq7) ].
assert (HEAPq7 : RHEAP st_7 L7 mq7).
{ eapply RHEAP_frame_proof; [exact HEAP_7| exact MUq7| exact WMq7|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS7| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq7 : rauxv_ok mq7 AB) by (eapply rauxv_ok_frame; [exact AUX_7| exact MUq7| exact WMq7| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq7 : rw_cells rsegs mq7 316332 [C4 errv_7]) by (eapply rw_cells_transport; [exact ERR_7| exact MUq7| exact WMq7| cbn; clear - SIMG; lia]).
assert (FRq7 : rw_cells rsegs mq7 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_7| exact MUq7| exact WMq7| cbn; clear - SLT SPR; lia]).
assert (STq7 : stk rsegs mq7 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_7| exact MUq7| exact WMq7| cbn; clear - SCE CLOv; lia]).
assert (TPq7 : rtables_pristine mq7) by (eapply rtables_pristine_munch; [exact TP_7| exact MUq7|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq7 : forall STEREO, DREP 0 STEREO mq7 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_7 STEREO)| exact MUq7| exact WMq7|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq7 : rheap_pres LB (bv_unsigned sp) m0 mq7).
{ eapply rheap_pres_trans; [exact PRES_7|]. eapply rheap_pres_of_munch; [exact MUq7| exact WMq7|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (ZSq7_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq7 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_7_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq7_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq7 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_7_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq7_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs mq7 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS_7_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA2 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq7_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs mq7 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_7_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA3 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq7_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs mq7 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_7_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA4 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq7_5 : forall p, r5 = Some p -> rblock_range A5 16 /\ rw_cells rsegs mq7 A5 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS_7_5 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA5 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (ZSq7_6 : forall p, r6 = Some p -> rblock_range A6 16 /\ rw_cells rsegs mq7 A6 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS_7_6 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq7| exact WMq7|].
destruct (SA6 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_7 HEAP_7 AUX_7 ERR_7 FR_7 ST_7 TP_7 RL_7 PRES_7 MUq7 WMq7 MI_7 ZS_7_0 ZS_7_1 ZS_7_2 ZS_7_3 ZS_7_4 ZS_7_5 ZS_7_6.
eapply implM_bind.
{ eapply (rcalloc_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc mq7 st_7 L7 (2 * sbm_lpcSize mo * 4) lo AB errv_7 HEAPq7 AUXq7);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact STq7| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERRq7| exact MIq7| exact TPE| reflexivity| reflexivity| unfold RSMALL_MAX; lia]. }
cbv beta. intros r7 st_8 msr7 sfH_; first [ sf_destruct 27%nat sfH_ as A7 y0_8 y1_8 y2_8 ya1_8 ya2_8 ya3_8 ya4_8 ya5_8 ya6_8 ya7_8 y3_8 y4_8 y5_8 y6_8 m_8 errv_8 -> MI_8 ST_8 ERR_8 AUX_8 HP_8 PSO_8 HEAP_8 ZR7 ZS0_8 | sf_fb; destruct sfH_ as (A7 & y0_8 & y1_8 & y2_8 & ya1_8 & ya2_8 & ya3_8 & ya4_8 & ya5_8 & ya6_8 & ya7_8 & y3_8 & y4_8 & y5_8 & y6_8 & m_8 & errv_8 & -> & MI_8 & ST_8 & ERR_8 & AUX_8 & HP_8 & PSO_8 & HEAP_8 & ZR7 & ZS0_8) ].
rewrite unsigned_lit in ST_8 by lia. rewrite unsigned_lit in HP_8 by lia. rewrite ret_pc_even by (clear; lia). rewrite ETP in ERR_8. unfold RERRNO in ERR_8.
change (mem_inv rsegs m_8) in MI_8. change (stk rsegs m_8 lo (bv_unsigned sp + -48)) in ST_8. change (rw_cells rsegs m_8 316332 [C4 errv_8]) in ERR_8.
apply (RHEAP_perm _ _ (L7 ++ oblk r7 A7 (2 * sbm_lpcSize mo * 4))) in HEAP_8; [| apply Permutation_app_comm].
set (L8 := L7 ++ oblk r7 A7 (2 * sbm_lpcSize mo * 4)) in HEAP_8.
assert (INS8 : In (blk, S, SBSTATE_SIZEOF) L8) by (subst L8; apply in_app_iff; left; exact INS7).
assert (INL8 : forall b, In b LBL -> In b L8) by (intros b Hb; subst L8; apply in_app_iff; left; apply INL7; exact Hb).
assert (INB8 : forall b, In b LB -> In b L8) by (intros b Hb; subst L8; apply in_app_iff; left; apply INB7; exact Hb).
assert (INr7 : forall p, r7 = Some p -> In (p, A7, (2 * sbm_lpcSize mo * 4)) L8) by (intros p E; subst L8; apply in_app_iff; right; rewrite E; left; reflexivity).
assert (INr0_8 : forall p, r0 = Some p -> In (p, A0, 256) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr0_7 p E)).
assert (INr1_8 : forall p, r1 = Some p -> In (p, A1, 256) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr1_7 p E)).
assert (INr2_8 : forall p, r2 = Some p -> In (p, A2, (sbm_subframeSize mo * 4)) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr2_7 p E)).
assert (INr3_8 : forall p, r3 = Some p -> In (p, A3, (sbm_lpcSize mo * 4)) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr3_7 p E)).
assert (INr4_8 : forall p, r4 = Some p -> In (p, A4, (sbm_lpcSize mo * 4)) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr4_7 p E)).
assert (INr5_8 : forall p, r5 = Some p -> In (p, A5, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr5_7 p E)).
assert (INr6_8 : forall p, r6 = Some p -> In (p, A6, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)) L8) by (intros p E; subst L8; apply in_app_iff; left; exact (INr6_7 p E)).
assert (INr7_8 := INr7).
assert (SA7 : forall p, r7 = Some p -> S + 160 <= A7 \/ A7 + 64 <= S).
{ intros p E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP_8) as NDk.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A7, (2 * sbm_lpcSize mo * 4)) (blk, S, SBSTATE_SIZEOF) HEAP_8 (INr7 p E) INS8) as [D|D].
{ subst L8. rewrite E, map_app in NDk. cbn [oblk map blk_id fst snd] in NDk |- *. apply not_eq_sym.
eapply (NoDup_app_in_neq _ _ _ _ NDk); [apply (in_map blk_id L7 (blk, S, SBSTATE_SIZEOF)); exact INS7| left; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
assert (X_8 : rw_cells rsegs m_8 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 0 A5 A6 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))).
{ eapply rheap_pres_rw_cells; [exact HP_8| exact Xq7|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS7| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (FR_8 : rw_cells rsegs m_8 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP_8| exact FRq7| left; cbn; lia]).
assert (TP_8 : rtables_pristine m_8) by (eapply rtables_pristine_rheap; [exact TPq7| exact HP_8]).
assert (RL_8 : forall STEREO, DREP 0 STEREO m_8 SL low LBL) by (intros STEREO; eapply decst_rep_rheap; [exact (RLq7 STEREO)| exact HP_8| exact INL7]).
assert (PRES_8 : rheap_pres LB (bv_unsigned sp) m0 m_8) by (eapply rheap_pres_trans; [exact PRESq7| eapply rheap_pres_weaken; [exact HP_8| lia| exact INB7]]).
assert (ZS_8_7 : forall p, r7 = Some p -> rblock_range A7 64 /\ rw_cells rsegs m_8 A7 [CB (Z.to_nat 64) (repeat (Z_to_bv 8 0) (Z.to_nat 64))]).
{ intros p E. destruct (ZS0_8 p E) as [BRk Zk]. rewrite ?NBS in BRk, Zk. cbn [Z.mul Pos.mul sbm_lpcSize] in BRk, Zk. split; [exact BRk| exact Zk]. }
assert (ZS_8_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs m_8 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq7_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A0, 256).
split; [exact (INr0_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_8_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs m_8 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZSq7_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A1, 256).
split; [exact (INr1_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_8_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs m_8 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZSq7_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A2, (sbm_subframeSize mo * 4)).
split; [exact (INr2_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_8_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs m_8 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq7_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A3, (sbm_lpcSize mo * 4)).
split; [exact (INr3_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_8_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs m_8 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZSq7_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A4, (sbm_lpcSize mo * 4)).
split; [exact (INr4_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_8_5 : forall p, r5 = Some p -> rblock_range A5 16 /\ rw_cells rsegs m_8 A5 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZSq7_5 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A5, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)).
split; [exact (INr5_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
assert (ZS_8_6 : forall p, r6 = Some p -> rblock_range A6 16 /\ rw_cells rsegs m_8 A6 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZSq7_6 p E) as [BRj Zj]. split; [exact BRj|]. eapply rheap_pres_rw_cells; [exact HP_8| exact Zj|]. right; right. exists (p, A6, (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4)).
split; [exact (INr6_7 p E)| cbn [blk_addr blk_size fst snd cells_size csize length Nat.add]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; lia]. }
clear Xq7 HEAPq7 AUXq7 ERRq7 FRq7 STq7 TPq7 RLq7 PRESq7 HP_8 MIq7 ZS0_8 ZSq7_0 ZSq7_1 ZSq7_2 ZSq7_3 ZSq7_4 ZSq7_5 ZSq7_6.

eapply (implM_evt rsegs _ _ _ (fun msq => exists mq,
msq = MS (mkR (Z_to_bv 64 0x2e5f4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y0_8 y1_8 y2_8 (Z_to_bv 64 S) (Z_to_bv 64 (sbm_lpcSize mo + 1073741824)) (Z_to_bv 64 A7) (Z_to_bv 64 1000) ya2_8 ya3_8 ya4_8 ya5_8 ya6_8 ya7_8 (Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 y3_8 y4_8 y5_8 y6_8) F0 (Z_to_bv 64 0x2e600) fc None mq (seg_rom rsegs)
/\ rw_cells rsegs mq S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 A7 A5 A6 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ munch [(S, S + 160)] m_8 mq /\ wmono rsegs m_8 mq /\ mem_inv rsegs mq)).
{ pose proof (munch_refl [(S, S + 160)] m_8) as MU. pose proof (wmono_refl rsegs m_8) as WM.
clear HEAP_8 PRES_8 RL_8. unfold sbx_cells in X_8.
step. lstep. lstep. apply evt_done; eexists; (split; [reflexivity|]); (split; [unfold sbx_cells; eassumption|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros msq8 sfH_; first [ sf_destruct 6%nat sfH_ as mq8 -> Xq8 MUq8 WMq8 MIq8 | sf_fb; destruct sfH_ as (mq8 & -> & Xq8 & MUq8 & WMq8 & MIq8) ]. unfold sbx_cells in Xq8.
assert (HEAPq8 : RHEAP st_8 L8 mq8).
{ eapply RHEAP_frame_proof; [exact HEAP_8| exact MUq8| exact WMq8|]. constructor; [|constructor]. right. right. exists (blk, S, SBSTATE_SIZEOF). split; [exact INS8| cbn; unfold SBSTATE_SIZEOF; clear - S0; lia]. }
assert (AUXq8 : rauxv_ok mq8 AB) by (eapply rauxv_ok_frame; [exact AUX_8| exact MUq8| exact WMq8| constructor; [cbn [fst snd]; unfold RAUXV_CELL; clear - SLT SB SIMG SPR; lia| constructor]]).
assert (ERRq8 : rw_cells rsegs mq8 316332 [C4 errv_8]) by (eapply rw_cells_transport; [exact ERR_8| exact MUq8| exact WMq8| cbn; clear - SIMG; lia]).
assert (FRq8 : rw_cells rsegs mq8 (bv_unsigned sp + -48) [CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply rw_cells_transport; [exact FR_8| exact MUq8| exact WMq8| cbn; clear - SLT SPR; lia]).
assert (STq8 : stk rsegs mq8 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST_8| exact MUq8| exact WMq8| cbn; clear - SCE CLOv; lia]).
assert (TPq8 : rtables_pristine mq8) by (eapply rtables_pristine_munch; [exact TP_8| exact MUq8|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; clear - Hx SIMG; lia).
assert (RLq8 : forall STEREO, DREP 0 STEREO mq8 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (RL_8 STEREO)| exact MUq8| exact WMq8|]. intros b x Hb Hx. pose proof (SAPL _ Hb) as DSA. cbn. clear - DSA Hx; lia. }
assert (PRESq8 : rheap_pres LB (bv_unsigned sp) m0 mq8).
{ eapply rheap_pres_trans; [exact PRES_8|]. eapply rheap_pres_of_munch; [exact MUq8| exact WMq8|]. intros x Hx CA. apply outside_single.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [clear - CA SLT; lia| clear - CA SIMG; lia|]. unfold in_block in Hab'. destruct (BLB _ Hb') as [B1 B2]. clear - Hab' B2; lia. }
assert (Z8_0 : forall p, r0 = Some p -> rblock_range A0 256 /\ rw_cells rsegs mq8 A0 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_8_0 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA0 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_1 : forall p, r1 = Some p -> rblock_range A1 256 /\ rw_cells rsegs mq8 A1 [CB (Z.to_nat 256) (repeat (Z_to_bv 8 0) (Z.to_nat 256))]).
{ intros p E. destruct (ZS_8_1 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA1 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_2 : forall p, r2 = Some p -> rblock_range A2 (sbm_subframeSize mo * 4) /\ rw_cells rsegs mq8 A2 [CB (Z.to_nat (sbm_subframeSize mo * 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (sbm_subframeSize mo * 4)))]).
{ intros p E. destruct (ZS_8_2 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA2 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_3 : forall p, r3 = Some p -> rblock_range A3 32 /\ rw_cells rsegs mq8 A3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_8_3 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA3 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_4 : forall p, r4 = Some p -> rblock_range A4 32 /\ rw_cells rsegs mq8 A4 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))]).
{ intros p E. destruct (ZS_8_4 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA4 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_5 : forall p, r5 = Some p -> rblock_range A5 16 /\ rw_cells rsegs mq8 A5 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS_8_5 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA5 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_6 : forall p, r6 = Some p -> rblock_range A6 16 /\ rw_cells rsegs mq8 A6 [CB (Z.to_nat 16) (repeat (Z_to_bv 8 0) (Z.to_nat 16))]).
{ intros p E. destruct (ZS_8_6 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA6 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
assert (Z8_7 : forall p, r7 = Some p -> rblock_range A7 64 /\ rw_cells rsegs mq8 A7 [CB (Z.to_nat 64) (repeat (Z_to_bv 8 0) (Z.to_nat 64))]).
{ intros p E. destruct (ZS_8_7 p E) as [BRj Zj]. split; [exact BRj|]. eapply rw_cells_transport; [exact Zj| exact MUq8| exact WMq8|].
destruct (SA7 p E) as [DSA|DSA]; cbn [cells_size csize length Nat.add disjoint_from fst snd]; rewrite ?repeat_length; pose proof BRj as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ Bn _ _ | sf_fb; destruct sfP_ as (_ & _ & Bn & _ & _) ]; clear - DSA Bn; lia. }
clear X_8 HEAP_8 AUX_8 ERR_8 FR_8 ST_8 TP_8 RL_8 PRES_8 MUq8 WMq8 MI_8 ZS_8_0 ZS_8_1 ZS_8_2 ZS_8_3 ZS_8_4 ZS_8_5 ZS_8_6 ZS_8_7.
assert (XEQ : SBCELLS (mkSBD blk mo (2 * sbm_frameSize mo) (sbm_frameSize mo) (sbm_subframeSize mo) (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo)) (sbm_lpcSize mo) 1 (lr * 2) 0 blk blk blk blk blk blk blk blk None 1 (sbm_defaultSubmode mo)) (SBA SL A0 A1 A2 A3 A4 A7 A5 A6) 0 (SBJ w0 w0 z4 z4 [] [] [] [] [] [] [] []) = (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 A0 A1 A2 A3 A4 A7 A5 A6 0 w0 w0 (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))) by (destruct Hmo as [-> | ->]; reflexivity).
assert (DDL3 : (dec_depth low <= 3)%nat) by (rewrite DD; destruct Hmo as [-> | ->]; cbn; lia).
pose proof (des_depth_le low DDL3) as DDEP.
unfold sb_init_fin; cbv zeta.
destruct r0 as [p0|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_0 p0 eq_refl) as [BR0 ZZ0]. pose proof BR0 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos0 _ _ Ace0 _ | sf_fb; destruct sfP_ as (Apos0 & _ & _ & Ace0 & _) ]. unfold alloc_ceiling in Ace0.
destruct r1 as [p1|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_1 p1 eq_refl) as [BR1 ZZ1]. pose proof BR1 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos1 _ _ Ace1 _ | sf_fb; destruct sfP_ as (Apos1 & _ & _ & Ace1 & _) ]. unfold alloc_ceiling in Ace1.
destruct r2 as [p2|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_2 p2 eq_refl) as [BR2 ZZ2]. pose proof BR2 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos2 _ _ Ace2 _ | sf_fb; destruct sfP_ as (Apos2 & _ & _ & Ace2 & _) ]. unfold alloc_ceiling in Ace2.
destruct r3 as [p3|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_3 p3 eq_refl) as [BR3 ZZ3]. pose proof BR3 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos3 _ _ Ace3 _ | sf_fb; destruct sfP_ as (Apos3 & _ & _ & Ace3 & _) ]. unfold alloc_ceiling in Ace3.
destruct r4 as [p4|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_4 p4 eq_refl) as [BR4 ZZ4]. pose proof BR4 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos4 _ _ Ace4 _ | sf_fb; destruct sfP_ as (Apos4 & _ & _ & Ace4 & _) ]. unfold alloc_ceiling in Ace4.
destruct r5 as [p5|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_5 p5 eq_refl) as [BR5 ZZ5]. pose proof BR5 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos5 _ _ Ace5 _ | sf_fb; destruct sfP_ as (Apos5 & _ & _ & Ace5 & _) ]. unfold alloc_ceiling in Ace5.
destruct r6 as [p6|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_6 p6 eq_refl) as [BR6 ZZ6]. pose proof BR6 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos6 _ _ Ace6 _ | sf_fb; destruct sfP_ as (Apos6 & _ & _ & Ace6 & _) ]. unfold alloc_ceiling in Ace6.
destruct r7 as [p7|].
2:{   cbv beta iota. apply implM_unr. }
destruct (Z8_7 p7 eq_refl) as [BR7 ZZ7]. pose proof BR7 as sfP_; first [ sf_destruct 5%nat sfP_ as Apos7 _ _ Ace7 _ | sf_fb; destruct sfP_ as (Apos7 & _ & _ & Ace7 & _) ]. unfold alloc_ceiling in Ace7.

cbv beta iota. apply implM_ret.
pose proof (conj ZZ0 (conj ZZ1 (conj ZZ2 (conj ZZ3 (conj ZZ4 (conj ZZ5 (conj ZZ6 ZZ7))))))) as ZALL; clear ZZ0 ZZ1 ZZ2 ZZ3 ZZ4 ZZ5 ZZ6 ZZ7.
pose proof (conj HEAPq8 (conj PRESq8 (conj RLq8 (conj TPq8 (conj AUXq8 ERRq8))))) as KEEP; clear HEAPq8 PRESq8 RLq8 TPq8 AUXq8 ERRq8.
unfold sbx_cells in Xq8.
pose proof (munch_refl [(S, S + 160)] mq8) as MU; pose proof (wmono_refl rsegs mq8) as WM.
lstep. lstep. step.
step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
match goal with H : stk rsegs mx lo _ |- _ => rename H into STF end;
match goal with H : mem_inv rsegs mx |- _ => rename H into MIF end;
match goal with H : rw_cells rsegs mx (bv_unsigned sp + -48) _ |- _ => rename H into FRF end;
match goal with H : rw_cells rsegs mx S _ |- _ => rename H into XF end;
match goal with H : munch _ mq8 mx |- _ => rename H into MUF end;
match goal with H : wmono rsegs mq8 mx |- _ => rename H into WMF end
end.
first [ sf_destruct 8%nat ZALL as ZZ0 ZZ1 ZZ2 ZZ3 ZZ4 ZZ5 ZZ6 ZZ7 | sf_fb; destruct ZALL as (ZZ0 & ZZ1 & ZZ2 & ZZ3 & ZZ4 & ZZ5 & ZZ6 & ZZ7) ]; first [ sf_destruct 6%nat KEEP as HEAPq8 PRESq8 RLq8 TPq8 AUXq8 ERRq8 | sf_fb; destruct KEEP as (HEAPq8 & PRESq8 & RLq8 & TPq8 & AUXq8 & ERRq8) ].
release_frame FRF STF (bv_unsigned sp).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mF _) =>
assert (HEAPF : RHEAP st_8 L8 mF) by (eapply RHEAP_frame_proof; [exact HEAPq8| exact MUF| exact WMF| constructor; [right; right; exists (blk, S, SBSTATE_SIZEOF); split; [exact INS8| cbn; unfold SBSTATE_SIZEOF; lia]| constructor]]);
assert (AUXF : rauxv_ok mF AB) by (eapply rauxv_ok_frame; [exact AUXq8| exact MUF| exact WMF| constructor; [cbn [fst snd]; unfold RAUXV_CELL; lia| constructor]]);
assert (ERRF : rw_cells rsegs mF 316332 [C4 errv_8]) by (first [assumption | eapply rw_cells_transport; [exact ERRq8| exact MUF| exact WMF| cbn; lia]]);
assert (TPF : rtables_pristine mF) by (eapply rtables_pristine_munch; [exact TPq8| exact MUF|]; intros x Hx; unfold RTABLES_LO, RTABLES_HI in Hx; cbn; lia);
assert (RLF : forall STEREO, DREP 0 STEREO mF SL low LBL) by (intros STEREO; eapply decst_rep_munch; [exact (RLq8 STEREO)| exact MUF| exact WMF|]; intros b x Hb Hx; pose proof (SAPL _ Hb); cbn; lia);
assert (PRESF : rheap_pres LB (bv_unsigned sp) m0 mF) by
(eapply rheap_pres_trans; [exact PRESq8|]; eapply rheap_pres_of_munch; [exact MUF| exact WMF|]; intros x Hx CA; apply outside_single;
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA;
destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [lia| lia| unfold in_block in Hab'; destruct (BLB _ Hb') as [B1 B2]; lia])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mF _) =>
assert (BZ0 : rw_cells rsegs mF A0 (f32 (repeat w0 (Z.to_nat 64)))) by (apply (zero_f32_recast _ _ 64 ltac:(lia)); eapply rw_cells_transport; [exact ZZ0| exact MUF| exact WMF| destruct (SA0 p0 eq_refl); cbn; lia]);
assert (BZ1 : rw_cells rsegs mF A1 (f32 (repeat w0 (Z.to_nat 64)))) by (apply (zero_f32_recast _ _ 64 ltac:(lia)); eapply rw_cells_transport; [exact ZZ1| exact MUF| exact WMF| destruct (SA1 p1 eq_refl); cbn; lia]);
assert (BZ2 : rw_cells rsegs mF A2 (f32 (repeat w0 (Z.to_nat (sbm_subframeSize mo))))) by (apply (zero_f32_recast _ _ (sbm_subframeSize mo) ltac:(lia)); eapply rw_cells_transport; [exact ZZ2| exact MUF| exact WMF| destruct (SA2 p2 eq_refl); cbn; rewrite ?repeat_length; lia]);
assert (BZ3 : rw_cells rsegs mF A3 (f32 (repeat w0 (Z.to_nat 8)))) by (apply (zero_f32_recast _ _ 8 ltac:(lia)); eapply rw_cells_transport; [exact ZZ3| exact MUF| exact WMF| destruct (SA3 p3 eq_refl); cbn; lia]);
assert (BZ4 : rw_cells rsegs mF A4 (f32 (repeat w0 (Z.to_nat 8)))) by (apply (zero_f32_recast _ _ 8 ltac:(lia)); eapply rw_cells_transport; [exact ZZ4| exact MUF| exact WMF| destruct (SA4 p4 eq_refl); cbn; lia]);
assert (BZ5 : rw_cells rsegs mF A5 (f32 (repeat w0 (Z.to_nat 4)))) by (apply (zero_f32_recast _ _ 4 ltac:(lia)); eapply rw_cells_transport; [exact ZZ5| exact MUF| exact WMF| destruct (SA5 p5 eq_refl); cbn; lia]);
assert (BZ6 : rw_cells rsegs mF A6 (f32 (repeat w0 (Z.to_nat 4)))) by (apply (zero_f32_recast _ _ 4 ltac:(lia)); eapply rw_cells_transport; [exact ZZ6| exact MUF| exact WMF| destruct (SA6 p6 eq_refl); cbn; lia]);
assert (BZ7 : rw_cells rsegs mF A7 (f32 (repeat w0 (Z.to_nat 16)))) by (apply (zero_f32_recast _ _ 16 ltac:(lia)); eapply rw_cells_transport; [exact ZZ7| exact MUF| exact WMF| destruct (SA7 p7 eq_refl); cbn; lia])
end.
clear ZZ0 ZZ1 ZZ2 ZZ3 ZZ4 ZZ5 ZZ6 ZZ7.
assert (XEQF : (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo)) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) (Z_to_bv 64 0) A0 A1 A2 A3 A4 A7 A5 A6 0 w0 (Z_to_bv 64 1000) (Z_to_bv 64 1) (sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo))) = SBCELLS (mkSBD blk mo (2 * sbm_frameSize mo) (sbm_frameSize mo) (sbm_subframeSize mo) (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo)) (sbm_lpcSize mo) 1 (lr * 2) 0 p0 p1 p2 p3 p4 p7 p5 p6 None 1 (sbm_defaultSubmode mo)) (SBA SL A0 A1 A2 A3 A4 A7 A5 A6) 0 (SBJ w0 (Z_to_bv 64 1000) z4 z4 (repeat w0 (Z.to_nat 64)) (repeat w0 (Z.to_nat 64)) (repeat w0 (Z.to_nat (sbm_subframeSize mo))) (repeat w0 (Z.to_nat 8)) (repeat w0 (Z.to_nat 8)) (repeat w0 (Z.to_nat 16)) (repeat w0 (Z.to_nat 4)) (repeat w0 (Z.to_nat 4)))) by (destruct Hmo as [-> | ->]; reflexivity).

lazymatch type of HEAPF with RHEAP _ ?L8v ?mF => assert (PERMG : Permutation L8v ((sb_blocks (mkSBD blk mo (2 * sbm_frameSize mo) (sbm_frameSize mo) (sbm_subframeSize mo) (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo)) (sbm_lpcSize mo) 1 (lr * 2) 0 p0 p1 p2 p3 p4 p7 p5 p6 None 1 (sbm_defaultSubmode mo)) S (SBA SL A0 A1 A2 A3 A4 A7 A5 A6) ++ LBL) ++ LB)) end.
{ subst L8 L7 L6 L5 L4 L3 L2 L1 L0. unfold sb_blocks. cbn [oblk app sbd_blk sbd_g0_mem sbd_g1_mem sbd_excBuf sbd_old_qlsp sbd_interp_qlpc sbd_pi_gain sbd_exc_rms sbd_mem_sp sbd_subframeSize a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er].
rewrite ?NBS. rewrite ?(Z.mul_comm (sbm_subframeSize mo) 4). change (4 * 4) with 16. change (sbm_lpcSize mo * 4) with 32. change (2 * sbm_lpcSize mo * 4) with 64.
repeat rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
match goal with |- Permutation ?AA (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?R) => change (Permutation AA ([c0; c1; c2; c3; c4; c5; c6; c7] ++ R)) end.
rewrite (app_assoc LBL LB). apply Permutation_app_comm. }
pose proof (RHEAP_perm _ _ _ _ HEAPF PERMG) as HEAPG.
apply evt_done. unfold rinit_post.
lazymatch goal with |- exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' errv', MS _ _ _ _ _ ?mF _ = _ /\ _ =>
sf_eexists 15%nat; first [ unshelve sf_eexists 4%nat; [ exact (F0) | exact (fc) | exact (mF) | exact (errv_8) | ] | sf_fb; exists F0, fc, mF, errv_8 ] end.
split; [reflexivity|]. split; [exact FRM|]. split; [exact MIF|]. split; [exact STF|]. split; [rewrite ETP; unfold RERRNO; exact ERRF|]. split; [exact AUXF|]. split; [exact PRESF|].
split; [rewrite PSO_8, PSO_7, PSO_6, PSO_5, PSO_4, PSO_3, PSO_2, PSO_1; exact PSO_0|].
exists S, (sb_blocks (mkSBD blk mo (2 * sbm_frameSize mo) (sbm_frameSize mo) (sbm_subframeSize mo) (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo)) (sbm_lpcSize mo) 1 (lr * 2) 0 p0 p1 p2 p3 p4 p7 p5 p6 None 1 (sbm_defaultSubmode mo)) S (SBA SL A0 A1 A2 A3 A4 A7 A5 A6) ++ LBL).
split; [reflexivity|]. split; [lia|]. split; [exact HEAPG|].
split.
{ intros STEREO. cbn [decst_rep]. fold (DREP 0 STEREO). first [ unshelve sf_eexists 3%nat; [ exact ((SBA SL A0 A1 A2 A3 A4 A7 A5 A6)) | exact ((SBJ w0 (Z_to_bv 64 1000) z4 z4 (repeat w0 (Z.to_nat 64)) (repeat w0 (Z.to_nat 64)) (repeat w0 (Z.to_nat (sbm_subframeSize mo))) (repeat w0 (Z.to_nat 8)) (repeat w0 (Z.to_nat 8)) (repeat w0 (Z.to_nat 16)) (repeat w0 (Z.to_nat 4)) (repeat w0 (Z.to_nat 4)))) | exact (LBL) | ] | sf_fb; exists (SBA SL A0 A1 A2 A3 A4 A7 A5 A6), (SBJ w0 (Z_to_bv 64 1000) z4 z4 (repeat w0 (Z.to_nat 64)) (repeat w0 (Z.to_nat 64)) (repeat w0 (Z.to_nat (sbm_subframeSize mo))) (repeat w0 (Z.to_nat 8)) (repeat w0 (Z.to_nat 8)) (repeat w0 (Z.to_nat 16)) (repeat w0 (Z.to_nat 4)) (repeat w0 (Z.to_nat 4))), LBL ].
split; [reflexivity|]. split; [apply Z.mod_divide; [lia|]; apply Z.mod_divide in S16; [| lia]; destruct S16 as [q Hq]; exists (2 * q); lia|]. split; [lia|].
split. { unfold sb_inv. cbn -[Z.mul Z.add Z.le Z.lt Z.pow Z.opp]. rewrite ELR. destruct Hmo as [-> | ->]; cbn; repeat split; try lia; auto. }
split. { unfold sb_junk_ok. cbn -[Z.of_nat Z.to_nat repeat length]. rewrite !repeat_length. repeat split; try reflexivity; lia. }
split; [rewrite <- XEQF; exact XF|]. split; [| exists 0; exact (RLF STEREO)].
unfold sb_bufs. cbn [a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].
repeat match goal with |- _ /\ _ => split end; assumption. }
split; [exact (RHEAP_blocks_nodup_proof _ _ _ HEAPG)|].
split; [reflexivity|]. split; [reflexivity|]. split; [cbn [dec_depth]; rewrite DD, MDP; reflexivity|].
split; [cbn -[Z.mul init_rate]; rewrite IRT, ELR; lia|]. split; [cbn; exact STO|].
cbn [dec_nestedR sbd_mode]. split; [rewrite DM; destruct Hmo as [-> | ->]; reflexivity| exact NES].
Qed.
