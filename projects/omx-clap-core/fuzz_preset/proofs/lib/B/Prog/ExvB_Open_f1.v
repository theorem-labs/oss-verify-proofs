(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit 4f18c75d4900 (base cold/h-rw-pre-7-b-ex_value-rebind): EXB carries exv_rm, the
   memnorm keep from the entry memory, across every run by ExvB_Loop_exw.v's _inv runners at P := exvl_P (e_mem E)
   and across the ex_ws call by its m-form post. Does not rest on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CI, the FRONT with a node to compare (e_v E <> 0):
   B entry + 0x374 (0x838a0) to the depth branch (entry + 0x3b8, `blt 32, dep + 1`), then
   - depth 32: to CX (entry + 0xa7c) with s5 = -1 (exo_cx_fin);
   - else the type check of v (entry + 0x3c4 .. 0x3f4: alignment UBSan check, ASan check of v, `lw type`, expected
     (c == '{') ? 6 : 5, `beq`): equal -> entry + 0x440 with vv = v, differs unchanged; different -> in->differs := 1
     and 152(s1) := 0 -> entry + 0x440 (exo_cm_fin).
   The symbolic engine is the table engine over B's whole-range listing (YCbqG SRr_run_tok_AJx / SRr_run_to_tok_AJx,
   B_prog_tbl; their _inv twins of ExvB_Loop_exw.v), the idioms and tactics of lib/B/Prog/ex_ws_x.v (restated
   in ExvB_Loop_exw.v). The three UBSan checks of the stretch (entry + 0x39c
   `blt dep + 1, dep`, + 0x3cc v & 7, and none else before + 0x440) and its four ASan checks (q + 16 twice, v, q + 32)
   are resolved inside the runs: the facts dep in [0, 32], v 8-aligned, and the shadow entries of q's 40 bytes
   (EXB's range_addressable) and v's 56 bytes (prhex_tree's). Engine stops measured on f8f98a95 (scratch probe):
   + 0x3b8 SR_branch BC_LT (SLit 32) (SOff 32 1); + 0x3f4 SR_branch BC_EQ (SOff 34 0) (expected).
   Rule 24: proves no function (kind: segment lemma). Numerals: 0x374, 0x440, 0xa7c (DERIVED: cut offsets); atom
   indices 2, 9, 11, 19-27, 32-35 (DERIVED: register numbers and the engine's extra atoms); 64, 144, 152, 160 (LENGTH:
   slot offsets); 0, 4, 8, 16, 20, 32, 36, 40, 56 (LENGTH: struct ex / node fields); 91, 123, 5, 6 (WORD); 3, 5 (LENGTH:
   alignments log2); 2 ^ 32, 2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64, 4096, 17592186044416 (LENGTH: bounds; 2 ^ 44, the shadow
   band); 0x7fff8000 (DERIVED: SHADOW_OFF). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_exw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Open_pure ExvB_Open_kt ExvB_Open_fin.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the stretch's symbolic states ---- *)
Definition EXO_CI : Z := exv_pc 0x374.
Definition EXO_CM : Z := exv_pc 0x440.
Definition EXO_CX : Z := exv_pc 0xa7c.
Definition exo_shx (e : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL e (SLit 3)) (SOff 25 0).
Definition exo_regs : list sv := sr_atoms.
Definition exo_SPF : afact := mkAF (2 ^ 46) (2 ^ 47 - 288) 5.
Definition exo_QF : afact := mkAF (2 ^ 46) (2 ^ 47 - 40) 3.
Definition exo_PF : afact := mkAF 4096 (2 ^ 47 - 2) 0.
Definition exo_VF : afact := mkAF 8 (2 ^ 47 - 56) 3.
Definition exo_rg1 : smem :=
[ YP09.mkRegion (Some 9%nat) 64 160 64 160
    [YP09.mkChunk 144 (CVal 8 (exo_shx (SOff 19 0))); YP09.mkChunk 152 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 11 0))];
  YP09.mkRegion (Some 19%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 35 0))];
  YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))] ].
Definition exo_fc1 : list (nat * afact) :=
[ (9%nat, exo_SPF); (19%nat, exo_QF); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (11%nat, exo_PF);
  (27%nat, mkAF 91 123 0); (32%nat, mkAF 0 32 0); (33%nat, exo_VF); (34%nat, mkAF 0 6 0); (35%nat, mkAF 0 1 0) ].
Definition ss_ci1 : sstate := mkSS EXO_CI exo_regs exo_rg1 None (mkFacts exo_fc1 [] []).
Definition exo_SH1 : list shent := [mkSHE 19 0 40; mkSHE 33 0 56].
(* the front with no node: no node region, 152(s1) holds 0 *)
Definition exo_rg0 : smem :=
[ YP09.mkRegion (Some 9%nat) 64 160 64 160
    [YP09.mkChunk 144 (CVal 8 (exo_shx (SOff 19 0))); YP09.mkChunk 152 (CVal 8 (SLit 0))];
  YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 11 0))];
  YP09.mkRegion (Some 19%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 35 0))] ].
Definition exo_fc0 : list (nat * afact) :=
[ (9%nat, exo_SPF); (19%nat, exo_QF); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (11%nat, exo_PF);
  (27%nat, mkAF 91 123 0); (32%nat, mkAF 0 32 0); (35%nat, mkAF 0 1 0) ].
Definition ss_ci0 : sstate := mkSS EXO_CI exo_regs exo_rg0 None (mkFacts exo_fc0 [] []).
Definition exo_SH0 : list shent := [mkSHE 19 0 40].
Definition exo_Bx : sv := SOff 25 0.

(* ---- pure helpers ---- *)
Lemma exo_denot_shx : forall E n z v sb, ew E n = Z_to_bv 64 v -> ew E 25 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= v + z < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (exo_shx (SOff n z)) = Z_to_bv 64 (sb + (v + z) / 8).
Proof.
intros E n z v sb Hn Hm Hv Hvz Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (exo_shx (SOff n z)))). f_equal.
change (U E (exo_shx (SOff n z)) = sb + (v + z) / 8). unfold exo_shx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia.
rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + z) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + z) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (v + z)) by (unfold M64; lia). rewrite (zcanon_id ((v + z) / 8)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma exo_expect_U : forall E c, ew E 27 = Z_to_bv 64 c -> (c = 91 \/ c = 123) ->
  U E (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 27 (-123)) (SLit 1)) (SLit 5)) = if c =? 123 then 6 else 5.
Proof. intros E c H Hc. rewrite !U_SAlu, U_SOff, H, !U_SLit. destruct Hc as [-> | ->]; vm_compute; reflexivity. Qed.

Lemma exo_lt32 : forall d, 0 <= d <= 32 -> branch_taken BC_LT (Z_to_bv 64 32) (Z_to_bv 64 (d + 1)) = (d =? 32).
Proof.
intros d Hd.
assert (A : forallb (fun x => Bool.eqb (branch_taken BC_LT (Z_to_bv 64 32) (Z_to_bv 64 (x + 1))) (x =? 32))
  (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A d). apply Bool.eqb_prop, A.
apply in_map_iff. exists (Z.to_nat d). split; [lia | apply in_seq; lia].
Qed.

Lemma exo_lt32_sv : forall E d, ew E 32 = Z_to_bv 64 d -> 0 <= d <= 32 ->
  branch_taken BC_LT (sv_denot E (SLit 32)) (sv_denot E (SOff 32 1)) = (d =? 32).
Proof. intros E d H Hd. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. apply exo_lt32. exact Hd. Qed.

Lemma exo_STK_ge : forall Ex, 320 <= exv_STK Ex.
Proof.
intros Ex. unfold exv_STK, STK_ex_value.
lazymatch goal with |- context [zmaxl ?l] => assert (Hz : 16 <= zmaxl l) by (vm_compute; discriminate) end.
lazymatch goal with |- context [Z.of_nat (S ?m) * ?f] => let f' := eval vm_compute in f in change f with f' end.
pose proof (Zle_0_nat (e_n Ex)). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma exo_node_hdr : forall m lblk p t D, PRH_Reader.pj_nodeR rsegs m lblk p t D ->
  p mod 8 = 0 /\ val_mem rsegs m p 4 (PjTree.tag t).
Proof.
intros m lblk p t D H. destruct t; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & nn & cap & ((Hal8 & _) & (_ & Htg) & _) & _); split; assumption.
Qed.

Ltac exo_awr Usp Uq :=
lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [ew ewset Nat.eqb] in Ha; rewrite ?Usp, ?Uq in Ha; left; lia | ]);
apply awr_ok_nil.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Let LAWS := eh_laws B ARx SK HYP.
Let RUN (mem0 : word -> option byte) := SRr_run_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).
Let RUNTO (mem0 : word -> option byte) := SRr_run_to_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).

(* the node at v is outside the shadow band *)
Lemma exo_home_app : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) v,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_home ly S Lam regs v 56 -> 2 ^ 46 <= spZ regs ->
  forall x, v <= x < v + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs v HAR HLED Hhome Hsp x Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
destruct Hhome as [(b & k & Hin & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]].
- pose proof HLED as (_ & _ & HB & _). rewrite Forall_forall in HB.
  destruct (HB (b, k) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
  destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & _ & _ & Happ & _).
  assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (_ & _ & Happ).
  pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- unfold SHADOW_OFF. lia.
Qed.


(* the front with a node to compare *)
Lemma exo_front1 : forall n, CUT_CX (fx := fx) B ARx SK n -> CUT_CM (fx := fx) B ARx SK n ->
  forall Ex lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos (c : Z),
  e_n Ex = n -> EXV_PRE B ARx Ex -> EXB B ARx SK Ex lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q Ex) (e_x0 Ex + exv_i1 Ex) (e_x0 Ex + exv_len Ex) (e_dep Ex) (e_scr Ex) (e_dl Ex) ->
  exv_i1 Ex < exv_len Ex -> nth (Z.to_nat (exv_i1 Ex)) (e_x Ex) 0 = c -> (c = 91 \/ c = 123) ->
  getr regs 10 = w64 (if c =? 123 then 125 else 93) -> getr regs 11 = w64 (e_x0 Ex + exv_i1 Ex) ->
  getr regs 27 = w64 c -> getr regs 21 = w64 (-1) ->
  getr regs 20 = w64 (shadow_addr (e_q Ex)) -> getr regs 22 = w64 (shadow_addr (e_q Ex + 8)) ->
  getr regs 23 = w64 (e_q Ex + 8) ->
  exv_spill Ex Wc memc 144 (shadow_addr (e_q Ex)) -> exv_spill Ex Wc memc 152 (e_v Ex) ->
  e_v Ex <> 0 ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x374) regs memc mdc) (EXV_POST B ARx SK Ex).
Proof.
intros n HX HM Ex lyc Sc Hpc Wc regs memc mdc k pos c Hn HPRE HB Hcur Hi1 Hnth Hcc R10 R11 R27 R21 R20 R22 R23
  S144 S152 Hv0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (exo_STK_ge Ex) as HSTK.
pose proof (exv_s1_le Ex) as ((S1a & S1b) & S1m).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & Hsrc0 & _ & Hlen3 & Hi0 & Hdep & _ & Hdl &
  _ & _ & _ & Hsq & Hv & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & Hm64).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
destruct Hsrc0 as (_ & Hx4 & Hxc & _).
destruct Hv as [Hv | (_ & _ & HDJ)]; [exfalso; exact (Hv0 Hv)|].
pose proof HB as (HJ & _ & _ & _ & HHp & _ & HRM0 & HLED & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 &
  _ & _ & _ & _ & _ & _ & _ & HQR & HTREE).
pose proof (proj2 HRM0) as HPM.
destruct HTREE as [Hv | (Hnd & Hhome & Hrav & Hhv)]; [exfalso; exact (Hv0 Hv)|].
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
pose proof Hcur as (V0 & V8 & V16 & V24 & V32).
unfold exv_sp, exv_STK in *.
set (q := e_q Ex) in *. set (s1 := exv_s1 Ex) in *. set (v := e_v Ex) in *.
set (p := e_x0 Ex + exv_i1 Ex) in *. set (dep := e_dep Ex) in *. set (dl := e_dl Ex) in *.
set (tg := PjTree.tag (e_t Ex)) in *.
assert (Hi1' : 0 <= exv_i1 Ex).
{ unfold exv_i1, exv_len, exv_X. pose proof (PjGrammar.skip_len (skipn (Z.to_nat (e_i0 Ex)) (e_x Ex))).
  pose proof (length_skipn (Z.to_nat (e_i0 Ex)) (e_x Ex)). lia. }
assert (Hsp0 : 0 <= spZ (e_regs Ex)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs Ex) 2%bv)); unfold spZ; lia).
assert (Hp_def : p = e_x0 Ex + exv_i1 Ex) by reflexivity.
assert (Hlen_def : exv_len Ex = Z.of_nat (length (e_x Ex))) by reflexivity.
assert (FOOT := exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam Ex) (e_peak Ex) (e_cnt Ex) (e_fail Ex)
  (e_ran Ex) (e_most Ex) (e_own Ex) regs v (e_t Ex) (e_D Ex) HAR HLED Hnd Hhome ltac:(lia)).
assert (Fv0 := FOOT v ltac:(left; lia)). assert (Fv1 := FOOT (v + 55) ltac:(left; lia)).
(* the node's header: 8-aligned, its type word the tree's tag *)
assert (Hhdr : v mod 8 = 0 /\ val_mem rsegs (mrestrict (w_H Wc) memc) v 4 tg /\ 0 <= tg <= 6).
{ destruct (exo_node_hdr _ _ _ _ _ Hnd) as (Hal8 & Htg). split; [exact Hal8|]. split; [exact Htg|].
  unfold tg. destruct (e_t Ex); cbn; lia. }
destruct Hhdr as (Hv8 & Vtg & Htg).
(* the node is apart from the frame window and the cursor *)
assert (Dvf : v + 4 <= s1 + 64 \/ s1 + 160 <= v).
{ destruct (Z_lt_le_dec v (s1 + 64)) as [Hl|Hl].
  - destruct (Z_le_gt_dec (v + 4) (s1 + 64)) as [Hl2|Hl2]; [left; exact Hl2|].
    destruct (HDJ (s1 + 64) ltac:(left; lia)) as (_ & _ & Hs & _). exfalso. apply Hs. lia.
  - destruct (Z_le_gt_dec (s1 + 160) v) as [Hl2|Hl2]; [right; exact Hl2|].
    destruct (HDJ v ltac:(left; lia)) as (_ & _ & Hs & _). exfalso. apply Hs. lia. }
assert (Dvq : v + 4 <= q \/ q + 40 <= v).
{ destruct (Z_lt_le_dec v q) as [Hl|Hl].
  - destruct (Z_le_gt_dec (v + 4) q) as [Hl2|Hl2]; [left; exact Hl2|].
    destruct (HDJ q ltac:(left; lia)) as (_ & Hs & _). exfalso. apply Hs. lia.
  - destruct (Z_le_gt_dec (q + 40) v) as [Hl2|Hl2]; [right; exact Hl2|].
    destruct (HDJ v ltac:(left; lia)) as (_ & Hs & _). exfalso. apply Hs. lia. }
assert (Hdep' : 0 <= dep <= 32) by exact Hdep.
assert (Hdl' : 0 <= dl <= 1) by (destruct Hdl as [-> | ->]; lia).
assert (Hc' : 91 <= c <= 123) by (destruct Hcc as [-> | ->]; lia).
(* the environment *)
remember (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) as En eqn:HE.
assert (AGE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) En) by (rewrite <- HE; apply env_agree_refl).
assert (E9 : ew En 9 = getr regs 9) by (subst En; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E10 : ew En 10 = getr regs 10) by (subst En; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew En 11 = Z_to_bv 64 p) by (subst En; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E19 : ew En 19 = Z_to_bv 64 q) by (subst En; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E24 : ew En 24 = Z_to_bv 64 (frame_addr lyc 1 pos)) by (subst En; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew En 25 = Z_to_bv 64 SHADOW_OFF) by (subst En; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E27 : ew En 27 = Z_to_bv 64 c) by (subst En; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew En 32 = Z_to_bv 64 dep) by (subst En; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew En 33 = Z_to_bv 64 v) by (subst En; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew En 34 = Z_to_bv 64 tg) by (subst En; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew En 35 = Z_to_bv 64 dl) by (subst En; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew En 9) = s1) by (rewrite E9, R9; apply unsigned_lit_small; lia).
assert (Uq : bv_unsigned (ew En 19) = q) by (rewrite E19; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew En 11) = p) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew En 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Uc : bv_unsigned (ew En 27) = c) by (rewrite E27; apply unsigned_lit_small; lia).
assert (Ud : bv_unsigned (ew En 32) = dep) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Uv : bv_unsigned (ew En 33) = v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Ut : bv_unsigned (ew En 34) = tg) by (rewrite E34; apply unsigned_lit_small; lia).
assert (Udl : bv_unsigned (ew En 35) = dl) by (rewrite E35; apply unsigned_lit_small; lia).
assert (Dq0 : sv_denot En (exo_shx (SOff 19 0)) = Z_to_bv 64 (SHADOW_OFF + q / 8)).
{ rewrite (exo_denot_shx En 19 0 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia). f_equal. lia. }
assert (Dq8 : sv_denot En (exo_shx (SOff 19 8)) = Z_to_bv 64 (SHADOW_OFF + (q + 8) / 8))
  by (rewrite (exo_denot_shx En 19 8 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia); reflexivity).
(* the symbolic state at CI *)
assert (HS : st_ok rsegs En ss_ci1 (restrict (w_H Wc) (mkst regs (Z_to_bv 64 EXO_CI) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ci1. apply exw_st_ok_full.
  - unfold exo_regs. rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exo_rg1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs En _ s1 144 8 (exo_shx (SOff 19 0)) (shadow_addr q));
          [rewrite Dq0; reflexivity | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S144].
      * apply (chunk_ok_val rsegs En _ s1 152 8 (SOff 33 0) v);
          [cbn [sv_denot]; rewrite Uv, Z.add_0_r; reflexivity | cbn; lia | zside | exact S152].
    + rewrite Uq. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ q 0 8 (SOff 11 0) p);
        [cbn [sv_denot]; rewrite Up, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact V0].
    + rewrite Uq. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ q 16 4 (SOff 32 0) dep);
        [cbn [sv_denot]; rewrite Ud, Z.add_0_r; reflexivity | cbn; lia | zside | exact V16].
    + rewrite Uq. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ q 32 4 (SOff 35 0) dl);
        [cbn [sv_denot]; rewrite Udl, Z.add_0_r; reflexivity | cbn; lia | zside | exact V32].
    + rewrite Uv. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ v 0 4 (SOff 34 0) tg);
        [cbn [sv_denot]; rewrite Ut, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vtg].
  - apply pairwise_disjoint_of_extents. unfold exo_rg1. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uq, Uv.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exo_fc1]. unfold afact_ok, exo_SPF, exo_QF, exo_PF, exo_VF. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uq, Usb, Up, Uc, Ud, Uv, Ut, Udl. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (HBx : U En exo_Bx = SHADOW_OFF) by (unfold exo_Bx; rewrite (U_atom En 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs exo_Bx exo_SH1 En (mrestrict (w_H Wc) memc)).
{ unfold exo_SH1. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H Wc) memc En exo_Bx 19 q 40 q 0 40 HQR HBx);
      [rewrite (U_atom En 19 q E19) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range rsegs (w_H Wc) memc En exo_Bx 33 v 56 v 0 56 Hrav HBx);
      [rewrite (U_atom En 33 v E33) by lia; reflexivity | lia | lia |].
    intros x Hx. apply (exo_home_app lyc Sc Hpc Wc memc mdc (e_Lam Ex) (e_peak Ex) (e_cnt Ex) (e_fail Ex)
      (e_ran Ex) (e_most Ex) (e_own Ex) regs v HAR HLED Hhome); [unfold spZ; rewrite R2; rewrite unsigned_lit_small by lia; lia | lia]. }
unfold cfg_at. change (w64 (exv_pc 0x374)) with (Z_to_bv 64 EXO_CI).
(* ---- run 1: CI to the depth branch ---- *)
exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
{ exo_awr Usp Uq. }
exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
  ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
rename KEPT into K1. rename HG into G1.
clear HF HFr.
exw_branch HS SHOK.
- (* depth 32: CX *)
  rewrite (exo_lt32_sv _ dep ltac:(exw_ew E32) Hdep') in Hc. apply Z.eqb_eq in Hc.
  exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXO_CX.
  { exo_awr Usp Uq. }
  exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
    ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
  rename KEPT into K2. rename HG into G2.
  clear HF HFr.
  lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
    assert (AG2 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) Ex')
      by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
    pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 21]%bv HS AG2
      ltac:(vm_compute; reflexivity)) as KR
  end.
  pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ0. cbn [ms_mem restrict] in RQ0.
  pose proof (exw_region_nth rsegs _ _ _ 2 _ HS eq_refl) as RQ16. cbn [ms_mem restrict] in RQ16.
  pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ32. cbn [ms_mem restrict] in RQ32.
  pmkst HS.
  unfold exvl_P in HPM.
  eapply (exo_cx_fin B ARx SK HYP n HX Ex lyc Sc Hpc Wc regs memc mdc k pos c); try eassumption.
  + apply (exo_kept_T1 Ex Wc memc _ 64 160); [unfold exv_sp, exv_STK; lia | lia |].
    intros a Ha Hz. rewrite K2, K1 by assumption. reflexivity.
  + intros a Ha. apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 11 0) p RQ0 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia)
      ltac:(zside)) as VQ. rewrite Z.add_0_r in VQ. exact VQ.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 16 4 (SOff 32 1) 33 RQ16 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ud; f_equal; lia) ltac:(cbn; lia)
      ltac:(zside)) as VQ. exact VQ.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 32 4 (SOff 35 0) dl RQ32 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Udl, Z.add_0_r; reflexivity) ltac:(cbn; lia)
      ltac:(zside)) as VQ. exact VQ.
- (* depth below 32: the type check *)
  rewrite (exo_lt32_sv _ dep ltac:(exw_ew E32) Hdep') in Hc. apply Z.eqb_neq in Hc. rename Hc into Hd32.
  assert (Hd1 : dep + 1 <= 32) by lia.
  exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
  { exo_awr Usp Uq. }
  exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
    ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
  rename KEPT into K2. rename HG into G2.
  clear HF HFr.
  exw_branch HS SHOK;
    rewrite branch_eq_U in Hc; rewrite (U_atom _ 34 tg ltac:(exw_ew E34)) in Hc by lia;
    rewrite (exo_expect_U _ c ltac:(exw_ew E27) Hcc) in Hc.
  + (* the node's type is the container's: vv = v, differs unchanged *)
    apply Z.eqb_eq in Hc.
    exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXO_CM.
    { exo_awr Usp Uq. }
    exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
      ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
    rename KEPT into K3. rename HG into G3.
    clear HF HFr.
    lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
      assert (AG3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) Ex')
        by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
      pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 11; 27; 20; 22; 23]%bv HS AG3
        ltac:(vm_compute; reflexivity)) as KR
    end.
    pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
    pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ0. cbn [ms_mem restrict] in RQ0.
    pose proof (exw_region_nth rsegs _ _ _ 2 _ HS eq_refl) as RQ16. cbn [ms_mem restrict] in RQ16.
    pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ32. cbn [ms_mem restrict] in RQ32.
    assert (Hfr : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
    { pose proof HJ as (HARn & _ & _ & _ & _ & Hfrs & _).
      assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
      destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HARn Hin1) as (F1 & F2 & _).
      change (fs_frame_bytes 1) with 128 in F2. lia. }
    pmkst HS.
    unfold exvl_P in HPM.
    eapply (exo_cm_fin B ARx SK HYP n HM Ex lyc Sc Hpc Wc regs memc mdc k pos c v dl); try eassumption.
    * exact (exv_dif_match Ex (c =? 123) Hv0 Hc).
    * apply (exo_kept_T1 Ex Wc memc _ 64 160); [unfold exv_sp, exv_STK; lia | lia |].
      intros a Ha Hz. rewrite K3, K2, K1 by assumption. reflexivity.
    * intros a Ha. apply (apresent_grows _ _ _ a G3), (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha.
    * pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 11 0) p RQ0 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia)
        ltac:(zside)) as VQ. rewrite Z.add_0_r in VQ. exact VQ.
    * exact (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 16 4 (SOff 32 1) (dep + 1) RQ16 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ud; reflexivity) ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 32 4 (SOff 35 0) dl RQ32 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Udl, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 64 8 (SOff 10 0) (if c =? 123 then 125 else 93) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E10, R10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (destruct (c =? 123); lia); reflexivity)
        ltac:(destruct (c =? 123); cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 96 8 (SOff 19 16) (q + 16) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity)
        ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(rewrite (exo_denot_shx _ 19 16 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) by (unfold SHADOW_OFF; lia); reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 120 8 (SOff 24 0) (frame_addr lyc 1 pos) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E24, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
        ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 144 8 (exo_shx (SOff 19 0)) (shadow_addr q) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(rewrite (exo_denot_shx _ 19 0 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) by (unfold SHADOW_OFF; lia);
              unfold shadow_addr; f_equal; f_equal; f_equal; lia)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 152 8 (SOff 33 0) v RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uv, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)).
  + apply Z.eqb_neq in Hc.
    exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXO_CM.
    { exo_awr Usp Uq. }
    exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
      ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
    rename KEPT into K3. rename HG into G3.
    clear HF HFr.
    lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
      assert (AG3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) Ex')
        by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
      pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 11; 27; 20; 22; 23]%bv HS AG3
        ltac:(vm_compute; reflexivity)) as KR
    end.
    pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
    pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ0. cbn [ms_mem restrict] in RQ0.
    pose proof (exw_region_nth rsegs _ _ _ 2 _ HS eq_refl) as RQ16. cbn [ms_mem restrict] in RQ16.
    pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ32. cbn [ms_mem restrict] in RQ32.
    assert (Hfr : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
    { pose proof HJ as (HARn & _ & _ & _ & _ & Hfrs & _).
      assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
      destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HARn Hin1) as (F1 & F2 & _).
      change (fs_frame_bytes 1) with 128 in F2. lia. }
    pmkst HS.
    unfold exvl_P in HPM.
    eapply (exo_cm_fin B ARx SK HYP n HM Ex lyc Sc Hpc Wc regs memc mdc k pos c 0 1); try eassumption.
    * right; reflexivity.
    * exact (exv_dif_mis Ex (c =? 123) Hv0 Hc).
    * apply (exo_kept_T1 Ex Wc memc _ 64 160); [unfold exv_sp, exv_STK; lia | lia |].
      intros a Ha Hz. rewrite K3, K2, K1 by assumption. reflexivity.
    * intros a Ha. apply (apresent_grows _ _ _ a G3), (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha.
    * pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 11 0) p RQ0 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia)
        ltac:(zside)) as VQ. rewrite Z.add_0_r in VQ. exact VQ.
    * exact (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 16 4 (SOff 32 1) (dep + 1) RQ16 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ud; reflexivity) ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 32 4 (SLit 1) 1 RQ32 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 64 8 (SOff 10 0) (if c =? 123 then 125 else 93) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E10, R10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (destruct (c =? 123); lia); reflexivity)
        ltac:(destruct (c =? 123); cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 96 8 (SOff 19 16) (q + 16) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity)
        ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(rewrite (exo_denot_shx _ 19 16 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) by (unfold SHADOW_OFF; lia); reflexivity)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 120 8 (SOff 24 0) (frame_addr lyc 1 pos) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E24, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
        ltac:(cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 144 8 (exo_shx (SOff 19 0)) (shadow_addr q) RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(rewrite (exo_denot_shx _ 19 0 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) by (unfold SHADOW_OFF; lia);
              unfold shadow_addr; f_equal; f_equal; f_equal; lia)
        ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)).
    * exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 152 8 (SLit 0) 0 RF
        ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)).
Qed.

(* the front with no node (v = 0) *)
Lemma exo_front0 : forall n, CUT_CX (fx := fx) B ARx SK n -> CUT_CM (fx := fx) B ARx SK n ->
  forall Ex lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos (c : Z),
  e_n Ex = n -> EXV_PRE B ARx Ex -> EXB B ARx SK Ex lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur Wc memc (e_q Ex) (e_x0 Ex + exv_i1 Ex) (e_x0 Ex + exv_len Ex) (e_dep Ex) (e_scr Ex) (e_dl Ex) ->
  exv_i1 Ex < exv_len Ex -> nth (Z.to_nat (exv_i1 Ex)) (e_x Ex) 0 = c -> (c = 91 \/ c = 123) ->
  getr regs 10 = w64 (if c =? 123 then 125 else 93) -> getr regs 11 = w64 (e_x0 Ex + exv_i1 Ex) ->
  getr regs 27 = w64 c -> getr regs 21 = w64 (-1) ->
  getr regs 20 = w64 (shadow_addr (e_q Ex)) -> getr regs 22 = w64 (shadow_addr (e_q Ex + 8)) ->
  getr regs 23 = w64 (e_q Ex + 8) ->
  exv_spill Ex Wc memc 144 (shadow_addr (e_q Ex)) -> exv_spill Ex Wc memc 152 (e_v Ex) ->
  e_v Ex = 0 ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x374) regs memc mdc) (EXV_POST B ARx SK Ex).
Proof.
intros n HX HM Ex lyc Sc Hpc Wc regs memc mdc k pos c Hn HPRE HB Hcur Hi1 Hnth Hcc R10 R11 R27 R21 R20 R22 R23
  S144 S152 Hv0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (exo_STK_ge Ex) as HSTK.
pose proof (exv_s1_le Ex) as ((S1a & S1b) & S1m).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & Hsrc0 & _ & Hlen3 & Hi0 & Hdep & _ & Hdl &
  _ & _ & _ & Hsq & Hv & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & Hm64).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
destruct Hsrc0 as (_ & Hx4 & Hxc & _).
pose proof HB as (HJ & _ & _ & _ & HHp & _ & HRM0 & HLED & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 &
  _ & _ & _ & _ & _ & _ & _ & HQR & HTREE).
pose proof (proj2 HRM0) as HPM.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
pose proof Hcur as (V0 & V8 & V16 & V24 & V32).
unfold exv_sp, exv_STK in *.
set (q := e_q Ex) in *. set (s1 := exv_s1 Ex) in *. set (v := e_v Ex) in *.
set (p := e_x0 Ex + exv_i1 Ex) in *. set (dep := e_dep Ex) in *. set (dl := e_dl Ex) in *.
set (tg := PjTree.tag (e_t Ex)) in *.
assert (Hi1' : 0 <= exv_i1 Ex).
{ unfold exv_i1, exv_len, exv_X. pose proof (PjGrammar.skip_len (skipn (Z.to_nat (e_i0 Ex)) (e_x Ex))).
  pose proof (length_skipn (Z.to_nat (e_i0 Ex)) (e_x Ex)). lia. }
assert (Hsp0 : 0 <= spZ (e_regs Ex)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs Ex) 2%bv)); unfold spZ; lia).
assert (Hp_def : p = e_x0 Ex + exv_i1 Ex) by reflexivity.
assert (Hlen_def : exv_len Ex = Z.of_nat (length (e_x Ex))) by reflexivity.
assert (Hdep' : 0 <= dep <= 32) by exact Hdep.
assert (Hdl' : 0 <= dl <= 1) by (destruct Hdl as [-> | ->]; lia).
assert (Hc' : 91 <= c <= 123) by (destruct Hcc as [-> | ->]; lia).
(* the environment *)
remember (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) as En eqn:HE.
assert (AGE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) En) by (rewrite <- HE; apply env_agree_refl).
assert (E9 : ew En 9 = getr regs 9) by (subst En; exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E10 : ew En 10 = getr regs 10) by (subst En; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew En 11 = Z_to_bv 64 p) by (subst En; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E19 : ew En 19 = Z_to_bv 64 q) by (subst En; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E24 : ew En 24 = Z_to_bv 64 (frame_addr lyc 1 pos)) by (subst En; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew En 25 = Z_to_bv 64 SHADOW_OFF) by (subst En; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E27 : ew En 27 = Z_to_bv 64 c) by (subst En; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew En 32 = Z_to_bv 64 dep) by (subst En; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew En 33 = Z_to_bv 64 v) by (subst En; exact (ew_Ereg_extra regs _ 1)).
assert (E35 : ew En 35 = Z_to_bv 64 dl) by (subst En; exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew En 9) = s1) by (rewrite E9, R9; apply unsigned_lit_small; lia).
assert (Uq : bv_unsigned (ew En 19) = q) by (rewrite E19; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew En 11) = p) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew En 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Uc : bv_unsigned (ew En 27) = c) by (rewrite E27; apply unsigned_lit_small; lia).
assert (Ud : bv_unsigned (ew En 32) = dep) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Uv : bv_unsigned (ew En 33) = v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Udl : bv_unsigned (ew En 35) = dl) by (rewrite E35; apply unsigned_lit_small; lia).
assert (Dq0 : sv_denot En (exo_shx (SOff 19 0)) = Z_to_bv 64 (SHADOW_OFF + q / 8)).
{ rewrite (exo_denot_shx En 19 0 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia). f_equal. lia. }
assert (Dq8 : sv_denot En (exo_shx (SOff 19 8)) = Z_to_bv 64 (SHADOW_OFF + (q + 8) / 8))
  by (rewrite (exo_denot_shx En 19 8 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia); reflexivity).
(* the symbolic state at CI *)
assert (Hv00 : v = 0) by exact Hv0. rewrite Hv00 in S152.
assert (HS : st_ok rsegs En ss_ci0 (restrict (w_H Wc) (mkst regs (Z_to_bv 64 EXO_CI) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ci0. apply exw_st_ok_full.
  - unfold exo_regs. rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exo_rg0. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs En _ s1 144 8 (exo_shx (SOff 19 0)) (shadow_addr q));
          [rewrite Dq0; reflexivity | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S144].
      * apply (chunk_ok_val rsegs En _ s1 152 8 (SLit 0) 0); [reflexivity | cbn; lia | zside | exact S152].
    + rewrite Uq. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ q 0 8 (SOff 11 0) p);
        [cbn [sv_denot]; rewrite Up, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact V0].
    + rewrite Uq. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ q 16 4 (SOff 32 0) dep);
        [cbn [sv_denot]; rewrite Ud, Z.add_0_r; reflexivity | cbn; lia | zside | exact V16].
    + rewrite Uq. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs En _ q 32 4 (SOff 35 0) dl);
        [cbn [sv_denot]; rewrite Udl, Z.add_0_r; reflexivity | cbn; lia | zside | exact V32].
  - apply pairwise_disjoint_of_extents. unfold exo_rg0. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uq.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exo_fc0]. unfold afact_ok, exo_SPF, exo_QF, exo_PF. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uq, Usb, Up, Uc, Ud, Udl. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (HBx : U En exo_Bx = SHADOW_OFF) by (unfold exo_Bx; rewrite (U_atom En 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs exo_Bx exo_SH0 En (mrestrict (w_H Wc) memc)).
{ unfold exo_SH0. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc En exo_Bx 19 q 40 q 0 40 HQR HBx);
    [rewrite (U_atom En 19 q E19) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (exv_pc 0x374)) with (Z_to_bv 64 EXO_CI).
(* ---- run 1: CI to the depth branch ---- *)
exw_run (RUN (e_mem Ex)) HS HJ SHOK HPM.
{ exo_awr Usp Uq. }
exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
  ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
rename KEPT into K1. rename HG into G1.
clear HF HFr.
exw_branch HS SHOK.
- (* depth 32: CX *)
  rewrite (exo_lt32_sv _ dep ltac:(exw_ew E32) Hdep') in Hc. apply Z.eqb_eq in Hc.
  exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXO_CX.
  { exo_awr Usp Uq. }
  exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
    ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
  rename KEPT into K2. rename HG into G2.
  clear HF HFr.
  lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
    assert (AG2 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) Ex')
      by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
    pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 21]%bv HS AG2
      ltac:(vm_compute; reflexivity)) as KR
  end.
  pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ0. cbn [ms_mem restrict] in RQ0.
  pose proof (exw_region_nth rsegs _ _ _ 2 _ HS eq_refl) as RQ16. cbn [ms_mem restrict] in RQ16.
  pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ32. cbn [ms_mem restrict] in RQ32.
  pmkst HS.
  unfold exvl_P in HPM.
  eapply (exo_cx_fin B ARx SK HYP n HX Ex lyc Sc Hpc Wc regs memc mdc k pos c); try eassumption.
  + apply (exo_kept_T1 Ex Wc memc _ 64 160); [unfold exv_sp, exv_STK; lia | lia |].
    intros a Ha Hz. rewrite K2, K1 by assumption. reflexivity.
  + intros a Ha. apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 11 0) p RQ0 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia)
      ltac:(zside)) as VQ. rewrite Z.add_0_r in VQ. exact VQ.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 16 4 (SOff 32 1) 33 RQ16 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ud; f_equal; lia) ltac:(cbn; lia)
      ltac:(zside)) as VQ. exact VQ.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 32 4 (SOff 35 0) dl RQ32 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Udl, Z.add_0_r; reflexivity) ltac:(cbn; lia)
      ltac:(zside)) as VQ. exact VQ.
- (* depth below 32: the type check *)
  rewrite (exo_lt32_sv _ dep ltac:(exw_ew E32) Hdep') in Hc. apply Z.eqb_neq in Hc. rename Hc into Hd32.
  assert (Hd1 : dep + 1 <= 32) by lia.
  exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM EXO_CM.
  { exo_awr Usp Uq. }
  exw_kept_of HFr (fun a => (s1 + 64 <= a < s1 + 160) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (q + 32 <= a < q + 36))
    ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?Uq, ?Uv in h).
  rename KEPT into K2. rename HG into G2.
  clear HF HFr.
  lazymatch type of HS with st_ok _ ?Ex' _ (restrict _ ?msF) =>
    assert (AG2 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [dep; v; tg; dl])) Ex')
      by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
    pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 11; 27; 20; 22; 23]%bv HS AG2
      ltac:(vm_compute; reflexivity)) as KR
  end.
  pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
  pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ0. cbn [ms_mem restrict] in RQ0.
  pose proof (exw_region_nth rsegs _ _ _ 2 _ HS eq_refl) as RQ16. cbn [ms_mem restrict] in RQ16.
  pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ32. cbn [ms_mem restrict] in RQ32.
  assert (Hfr : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
  { pose proof HJ as (HARn & _ & _ & _ & _ & Hfrs & _).
    assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
    destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HARn Hin1) as (F1 & F2 & _).
    change (fs_frame_bytes 1) with 128 in F2. lia. }
  pmkst HS.
  unfold exvl_P in HPM.
  eapply (exo_cm_fin B ARx SK HYP n HM Ex lyc Sc Hpc Wc regs memc mdc k pos c 0 dl); try eassumption.
  + exact (exv_dif_v0 Ex (c =? 123) Hv0).
  + apply (exo_kept_T1 Ex Wc memc _ 64 160); [unfold exv_sp, exv_STK; lia | lia |].
    intros a Ha Hz. rewrite K2, K1 by assumption. reflexivity.
  + intros a Ha. apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha.
  + pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 11 0) p RQ0 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up, Z.add_0_r; reflexivity) ltac:(cbn; lia)
      ltac:(zside)) as VQ. rewrite Z.add_0_r in VQ. exact VQ.
  + exact (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 16 4 (SOff 32 1) (dep + 1) RQ16 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Ud; reflexivity) ltac:(cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 32 4 (SOff 35 0) dl RQ32 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Udl, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 64 8 (SOff 10 0) (if c =? 123 then 125 else 93) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E10, R10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (destruct (c =? 123); lia); reflexivity)
      ltac:(destruct (c =? 123); cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 96 8 (SOff 19 16) (q + 16) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Uq; reflexivity)
      ltac:(cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 104 8 (exo_shx (SOff 19 16)) (shadow_addr (q + 16)) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(rewrite (exo_denot_shx _ 19 16 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) by (unfold SHADOW_OFF; lia); reflexivity)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 120 8 (SOff 24 0) (frame_addr lyc 1 pos) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E24, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
      ltac:(cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 144 8 (exo_shx (SOff 19 0)) (shadow_addr q) RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(rewrite (exo_denot_shx _ 19 0 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) by (unfold SHADOW_OFF; lia);
            unfold shadow_addr; f_equal; f_equal; f_equal; lia)
      ltac:(unfold shadow_addr, SHADOW_OFF; cbn; lia) ltac:(zside)).
  + exact (exw_field rsegs _ _ 9%nat s1 _ _ _ _ _ 152 8 (SLit 0) 0 RF
      ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)).
Qed.
End f.
