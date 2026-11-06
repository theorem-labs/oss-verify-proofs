(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgE01M.v at 5d5b79394a17; ported to reac-pw/fuzz_rate image A: module paths and names changed (rl_ to rt_, rl_env to rt_renv, RPgHarn to RtPgSeg, RPgE01D to RtPgE01D, rm_ to rtm_), rate's numbers (R - S is -0x1e0 or -0x1f0, the trampoline 0x52bb4, ra 0x809e0, 56 frame-shadow bytes, the six ranges of hi_w1), the statement taken in RtPgE01D's continuation form (the cut rh_cut_C1 is handed to the rh_from_C1 premise through YA0n SRr_bind), and the new conjuncts of RtPgSeg rh_common (the new block not among the entry's, the header tie and bounds); the freshness argument follows proofs/reac-pw/fuzz_role/lib/A/RPgX01.v rx_fresh at 9bffaa83ff88. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01M.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's trampoline 0x52c0c and ra 0x80ae4, R - S is -0x220 or -0x230, the class-4 frame
   (1024 bytes, 128 shadow bytes, the flag pointer word at F + 0x3f8, the 88-byte pattern rsb_P0), C1's values and
   write window of image B's record (the stack cells R + 0x30 .. R + 0x148), the harness records of lib/AU/RtPgSegB.v
   and the kits of lib/AU/RtPgMemB.v and lib/AU/RtPgStepsB.v (rhb_, rsb_, rtmb_, rtsb_ names). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01MB.v at 48db065d2b9c; for reac-pw/fuzz_role
   image B (fuzz_role.asan-ubsan): module paths and names back to role's (rt_ to rl_, rt_renv to rl_env, rhb_ to rh_,
   rtmb_ to rm_, rtsb_ to rl_); role B's trampoline 0x524c0 and ra 0x802c4, R - S is -0x200 or -0x210, C1's values
   and write ranges of lib/AU/RPgImgA.v role_himg_B (the one stack cell R + 0x40, the five ranges of hi_w1), the
   frame pattern hi_shA role_himg_B, the flags byte's bound in place of rate's header bounds; the stack bound
   0x210. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the last part CALL of segment
   S_E01 of the walk of LLVMFuzzerTestOneInput (0x80020), from the `jal` of malloc(19744) at 0x802c0 (pc 0x524c0, the
   malloc trampoline, ra = 0x802c4) to C1 0x802c4. It proves lib/AU/RPgE01D.v's e01b_call_stmt: from the call state
   e01b_call_facts, the call (lib/Reusable YCbq aj_malloc_at04) reaches a state at C1 where lib/AU/RPgHarn.v's cut
   rh_cut_C1 holds, and the premise rh_from_C1 takes the run on from there. Proves no function on its own (kind:
   segment lemma).

   THE CALL. The frame chain at the call is the entry frame pushed on the entry's chain (the `sd ra` / `sd s0` saves
   at S - 8 / S - 16 that rh_kept carries, the caller's chain from afn_pre kept by the journal above S): one record
   (S, RA_LLVMF, s0 of the entry) when S + 16 < ly_top, else none; the trace statement e01b_trace_stmt covers both
   shapes. sp = R = 32 * ((S - 0x200) / 32), so the offset R - S is -0x200 or -0x210 (16-aligned) and the
   allocator's stack [R - ASTACK, R) lies inside the entry's window when 0x210 + ASTACK <= LLVMF_STK.

   C1. The cut's facts come from the rule's post: the journal at one event, the block list with (pp, 19744)
   appended (pp not among the entry's blocks: the allocator's blocks are pairwise apart, AR's separation law), the
   callee-saved registers kept and a0 = pp; every byte at or above R kept (acall_kept's stack clause: the 13 saves,
   R + 0x40); the frame's bytes and its shadow bytes kept (acall_kept's frame clause: the new block is apart from the
   frame by AR's separation law and from the frame's shadow because a block lies in the application range); the
   input kept (acall_kept's block clause: the input block and the new block are two members of the C1 block list,
   so they are apart), with its shadow facts from AR's shadow law at C1, and apart from each range of hi_w1 (the
   frame, its shadow, the stack at or above R) and from pp. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YG0s YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgHarn RPgE01D RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== words and bytes ======================================== *)
Lemma e01mb_urange : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. exact (bv_unsigned_in_range 64 w). Qed.
Lemma e01mb_umod : forall w : word, bv_unsigned w mod 2 ^ 64 = bv_unsigned w.
Proof. intros w. apply Z.mod_small. exact (e01mb_urange w). Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01mb_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.
Lemma e01mb_getr_u : forall (regs : bvmap 5 word) r v,
getr regs (Z_to_bv 5 r) = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr regs (Z_to_bv 5 r)) = v.
Proof. intros regs r v H Hv. rewrite H. apply e01mb_u64. exact Hv. Qed.
Lemma e01mb_pres : forall (r1 r2 : bvmap 5 word) r v,
aregs_preserved r1 r2 -> acallee_saved r -> getr r1 (Z_to_bv 5 r) = w64 v -> getr r2 (Z_to_bv 5 r) = w64 v.
Proof. intros r1 r2 r v P Hr H. rewrite (P r Hr). exact H. Qed.
(* An 8-byte cell as the frame-chain reader sees it. *)
Lemma e01mb_rdword : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (Hb : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia. }
assert (B0 : aview segs H mem a = Some (YG0f.le_byte v 8 0)) by (rewrite <- (Hb 0%nat) by lia; f_equal; lia).
assert (B1 : aview segs H mem (a + 1) = Some (YG0f.le_byte v 8 1)) by (rewrite <- (Hb 1%nat) by lia; f_equal; lia).
assert (B2 : aview segs H mem (a + 2) = Some (YG0f.le_byte v 8 2)) by (rewrite <- (Hb 2%nat) by lia; f_equal; lia).
assert (B3 : aview segs H mem (a + 3) = Some (YG0f.le_byte v 8 3)) by (rewrite <- (Hb 3%nat) by lia; f_equal; lia).
assert (B4 : aview segs H mem (a + 4) = Some (YG0f.le_byte v 8 4)) by (rewrite <- (Hb 4%nat) by lia; f_equal; lia).
assert (B5 : aview segs H mem (a + 5) = Some (YG0f.le_byte v 8 5)) by (rewrite <- (Hb 5%nat) by lia; f_equal; lia).
assert (B6 : aview segs H mem (a + 6) = Some (YG0f.le_byte v 8 6)) by (rewrite <- (Hb 6%nat) by lia; f_equal; lia).
assert (B7 : aview segs H mem (a + 7) = Some (YG0f.le_byte v 8 7)) by (rewrite <- (Hb 7%nat) by lia; f_equal; lia).
unfold rdword. rewrite B0, B1, B2, B3, B4, B5, B6, B7. cbv beta iota. f_equal. apply le_bytes8. exact Hr.
Qed.
End w.

(* ======================================== the geometry ======================================== *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* R = 32 * ((S - 0x200) / 32) with S 16-aligned: R - S is -0x200 or -0x210. *)
Lemma e01mb_geo : forall S R, S mod 16 = 0 -> R = 32 * ((S - RH_RSZ) / 32) ->
R + 0x200 <= S /\ S <= R + 0x210 /\ (R - S) mod 16 = 0 /\ S mod 8 = 0.
Proof. intros S R H16 ->. unfold RH_RSZ. split; [lia|]. split; [lia|]. split; lia. Qed.
Section g. Context {rc : YM05.RunCeil}.
(* The 128 shadow bytes of a frame below alloc_ceiling are not in any application range (a block's range). *)
Lemma e01mb_sh_app : forall F i p n, 4096 <= F -> F + 1024 <= alloc_ceiling -> 0 <= i < 128 -> in_app p n ->
~ (p <= shadow_addr F + i < p + n).
Proof.
intros F i p n HF1 HF2 Hi Happ. pose proof alloc_ceiling_value as [HC _].
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ. unfold shadow_addr, SHADOW_OFF. lia.
Qed.
End g.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ======================================== the cut's parts ======================================== *)
(* The run's quantities at C1: those of the call state with pp filled in. *)
Definition e01mb_env (e : rl_env) (pp : Z) : rl_env :=
RLEnv (e_S e) (e_R e) (e_F e) pp (e_pod e) (e_len e) (e_fl e) (e_src e) (e_left e).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* C1's values: a0 = pp from the call, the others (hi_L1 but its first entry: s0, s1, s2 .. s7, s10, s11 and the
   cell R + 0x40) kept across it. *)
Lemma e01mb_cut_call : forall H mem H' mem' regs regs' e pp,
rl_cut rsegs H mem regs e (tl (hi_L1 role_himg_B)) ->
aregs_preserved regs regs' ->
(forall a, e_R e <= a < e_R e + 0x48 -> aview rsegs H' mem' a = aview rsegs H mem a) ->
getr regs' (Z_to_bv 5 10) = w64 pp ->
rl_cut rsegs H' mem' regs' (e01mb_env e pp) (hi_L1 role_himg_B).
Proof.
intros H mem H' mem' regs regs' e pp Hc P KR H10. unfold aregs_preserved in P.
unfold rl_cut in *. cbn [hi_L1 role_himg_B tl] in *.
repeat match goal with Hc : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in Hc as [? Hc] end.
cbn [fst snd rl_at] in *.
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd rl_at].
all: first
[ cbn [rl_xv e01mb_env e_pp]; rewrite Z.add_0_r; exact H10
| erewrite P; [eassumption | unfold acallee_saved; lia]
| eapply val_mem_kept; [|eassumption]; intros k Hk; apply KR; cbn [rl_xv e01mb_env e_R]; lia ].
Qed.

(* The carried cells (the 13 saves, the flag pointer word) kept across the call. *)
Lemma e01mb_kept_call : forall (hx : rh_hcx rsegs) pos e pp (W : world rsegs) mem regs (W' : world rsegs) mem' regs',
rh_kept rsegs hx pos e W mem regs ->
(forall j, (j < 13)%nat -> forall i, 0 <= i < 8 ->
 aview rsegs (w_H W') mem' (e_S e + (-8 - 8 * Z.of_nat j) + i) =
 aview rsegs (w_H W) mem (e_S e + (-8 - 8 * Z.of_nat j) + i)) ->
(forall i, 0 <= i < 8 -> aview rsegs (w_H W') mem' (e_F e + 0x3f8 + i) = aview rsegs (w_H W) mem (e_F e + 0x3f8 + i)) ->
rh_kept rsegs hx pos (e01mb_env e pp) W' mem' regs'.
Proof.
intros hx pos e pp W mem regs W' mem' regs' Hk KS KF.
unfold rh_kept, rh_cells in *. rewrite Forall_forall in *. intros f Hf. pose proof (Hk f Hf) as Hf'.
apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
- unfold rh_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
  cbn [fst snd rl_at rl_xv e01mb_env e_S] in *.
  eapply val_mem_kept; [|exact Hf']. intros k Hk'. apply KS; lia.
- cbn [fst snd rl_at rl_xv e01mb_env e_F] in *.
  eapply val_mem_kept; [|exact Hf']. intros k Hk'. apply KF. lia.
Qed.

(* role_build_contract's input premises at C1, from e01b_in at the call: nothing left, or the input lies in one
   entry block, which is apart from the new block, the frame, its shadow and the real frame's stack. *)
Lemma e01mb_input : forall (hx : rh_hcx rsegs) (W : world rsegs) mem e rest ly2 S2 (W2 : world rsegs) mem2 md2 pp,
e01b_in B hx W mem e rest ->
AR rsegs B ly2 S2 W2 mem2 md2 ->
ablocks B ly2 S2 = ablocks B (h_ly rsegs hx) (h_S rsegs hx) ++ [(pp, Layout.PP_SIZE)] ->
(forall b m i, In (b, m) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) -> 0 <= i < req_size m ->
 ~ (pp <= b + i < pp + req_size Layout.PP_SIZE) -> aview rsegs (w_H W2) mem2 (b + i) = aview rsegs (w_H W) mem (b + i)) ->
(forall p n, In (p, n) (ablocks B ly2 S2) -> zdisjoint (p, req_size n) (e_F e, 1024)) ->
alloc_ceiling + ASTACK <= e_R e -> 4096 <= e_F e -> e_F e + 1024 <= alloc_ceiling ->
rh_input rsegs W2 mem2 (e01mb_env e pp) rest.
Proof.
intros hx W mem e rest ly2 S2 W2 mem2 md2 pp Hin HAR2 Eab2 KB HFr HRc HF1 HF2.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hin as (EL & Hg & Hsrc & Hsrc63 & Hamr & Hcase).
unfold rh_input. cbn [e01mb_env e_left e_src e_R e_F e_pp].
destruct Hcase as [EL0 | (p & n & Hpn & Hp1 & Hp2)].
- destruct rest as [|x rest']; [|cbn [length] in EL; lia].
  split; [exact EL|]. split; [cbn [map]; apply garr8_nil|].
  split; [intros a Ha; exfalso; lia|]. split; [exact Hsrc|]. split; [exact Hsrc63|]. split; [exact Hamr|].
  split; [intros H0; exfalso; lia|]. intros a Ha. exfalso. lia.
- assert (Hp2' : In (p, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; left; exact Hpn).
  destruct (rm_blk_ra rsegs B ly2 S2 W2 mem2 md2 p n (e_src e) (e_left e) HAR2 Hp2' Hp1 Hp2) as [Hra Hhull].
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hp2') as (_ & _ & Hceil & Happ & _).
  pose proof (HFr p n Hp2') as HdF. unfold zdisjoint in HdF. cbn [fst snd] in HdF.
  assert (HdP : zdisjoint (block_rng (p, n)) (block_rng (pp, Layout.PP_SIZE))).
  { apply in_split in Hpn as (l1 & l2 & E).
    apply (sep_blocks_pos rsegs B LAWS ly2 S2 W2 mem2 md2 (p, n) (pp, Layout.PP_SIZE) l1 l2 [] HAR2).
    rewrite Eab2, E, <- app_assoc. reflexivity. }
  assert (Ereq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  unfold zdisjoint, block_rng in HdP. cbn [fst snd] in HdP. rewrite Ereq in HdP.
  split; [exact EL|].
  split.
  { change (rm_bytes rsegs (w_H W2) mem2 (e_src e) rest). apply (rm_bytes_kept rsegs (w_H W) mem); [exact Hg|].
    intros x Hx. rewrite <- EL in Hx. replace x with (p + (x - p)) by lia.
    eapply KB; [exact Hpn | lia | rewrite Ereq; lia]. }
  split; [exact Hra|]. split; [exact Hsrc|]. split; [exact Hsrc63|]. split; [exact Hamr|]. split; [exact Hhull|].
  intros a Ha. assert (Has : ASTACK = 16384) by reflexivity. split; [|split].
  + unfold T_SEG_STK. lia.
  + unfold rl_inw. cbn [hi_w1 role_himg_B]. rewrite !Exists_cons, Exists_nil.
    cbn [fst snd rl_xv e01mb_env e_F e_R].
    intros [X | [X | [X | [X | [X | []]]]]].
    * lia.
    * apply (e01mb_sh_app (e_F e) (a - shadow_addr (e_F e)) p (req_size n) HF1 HF2); [lia | exact Happ | lia].
    * lia.
    * lia.
    * lia.
  + lia.
Qed.

(* The new block is not one of the entry's: two members of the C1 block list are apart, and a block is not apart
   from itself (the argument of role's RPgX01.v rx_fresh). *)
Lemma e01mb_fresh : forall ly2 S2 (W2 : world rsegs) mem2 md2 (bl0 : list (Z * Z)) pp,
AR rsegs B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = bl0 ++ [(pp, Layout.PP_SIZE)] ->
~ In (pp, Layout.PP_SIZE) bl0.
Proof.
intros ly2 S2 W2 mem2 md2 bl0 pp HAR2 Eab2 Hin0.
pose proof (AR_laws_ok rsegs B) as LAWS.
apply in_split in Hin0 as (l1 & l2 & El).
pose proof (sep_blocks_pos rsegs B LAWS ly2 S2 W2 mem2 md2 (pp, Layout.PP_SIZE) (pp, Layout.PP_SIZE) l1 l2 [] HAR2
  ltac:(rewrite Eab2, El, <- app_assoc; reflexivity)) as Hd.
assert (Ereq : req_size Layout.PP_SIZE = 19744) by reflexivity.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Ereq in Hd. lia.
Qed.
End c.

(* ======================================== the call ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis HBmalloc : pc_wrap_malloc (as_code B) = 0x524c0.
Hypothesis HTRACE : e01b_trace_stmt B RA_LLVMF.
Hypothesis HSTK : 0x210 + ASTACK <= LLVMF_STK.
Hypothesis HEV : 1 <= EV_LIB.
Hypothesis HLIVE : Layout.PP_SIZE <= LIVE_LIB.
Theorem e01b_call_ok : e01b_call_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx POST HBASE HFROM pos e rest lyc Sc W regsT memc mdc HCALL.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof alloc_ceiling_value as (HCv & _). assert (Has : ASTACK = 16384) by reflexivity.
destruct HCALL as (HJ & Hfrc & Eab & Hgeo & Hra & Hsp & Hgp & Htp & Ha0 & Hcut & Hfsh & Hhok & Hhdr & Hkept & Hin).
destruct HBASE as (HPRE & HraE & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & Hlive0 & _).
pose proof HPRE as (_ & _ & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof Hstk0 as (Hal16 & HST0 & Hceil0 & Hslo & Hshi & H47 & _ & _ & Htop2).
pose proof HJ as (_ & Hlyc & _ & _ & _ & _ & Hnevc & _ & JK1 & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & EFc & _ & _ & Etopc & _).
pose proof Hgeo as (ES & ER & EF).
assert (ER' : e_R e = 32 * ((spZ (h_regs rsegs hx) - RH_RSZ) / 32)) by (rewrite ER, ES; reflexivity).
destruct (e01mb_geo _ _ Hal16 ER') as (HR1 & HR2 & HRo & Hal8). clear ER'.
assert (HRc : alloc_ceiling + ASTACK <= e_R e) by lia.
assert (HS47 : spZ (h_regs rsegs hx) <= 2 ^ 47) by lia.
assert (HspT : spZ regsT = e_R e) by (unfold spZ; rewrite Hsp; apply e01mb_u64; lia).
assert (HraT : raZ regsT = E01B_MALLOC_RA) by (unfold raZ; rewrite Hra; apply e01mb_u64; unfold E01B_MALLOC_RA; lia).
(* s0 = S at the call (C1's (LReg 8, XS)) *)
pose proof Hcut as Hc'. unfold rl_cut in Hc'. cbn [hi_L1 role_himg_B tl] in Hc'.
apply Forall_cons_iff in Hc' as [C8 _].
assert (Hs0T : s0Z regsT = spZ (h_regs rsegs hx)).
{ rewrite <- ES. unfold s0Z. exact (e01mb_getr_u regsT 8 (e_S e) C8 ltac:(lia)). }
(* the entry's ra and s0 in their save slots S - 8, S - 16 *)
pose proof Hkept as Hk'. unfold rh_kept, rh_cells, rh_saves_L in Hk'. cbn [seq map app] in Hk'.
apply Forall_cons_iff in Hk' as [K0 Hk']. apply Forall_cons_iff in Hk' as [K1 _].
assert (Hs8 : rdword (aview rsegs (w_H W) memc) (spZ (h_regs rsegs hx) - 8) = Some RA_LLVMF).
{ rewrite <- HraE. unfold raZ. apply e01mb_rdword; [|apply e01mb_urange].
  rewrite <- (e01mb_umod (getr (h_regs rsegs hx) 1)).
  replace (spZ (h_regs rsegs hx) - 8) with (e_S e + (-8 - 8 * Z.of_nat 0)) by (rewrite ES; lia).
  exact K0. }
assert (Hs16 : rdword (aview rsegs (w_H W) memc) (spZ (h_regs rsegs hx) - 16) = Some (s0Z (h_regs rsegs hx))).
{ unfold s0Z. apply e01mb_rdword; [|apply e01mb_urange].
  rewrite <- (e01mb_umod (getr (h_regs rsegs hx) 8)).
  replace (spZ (h_regs rsegs hx) - 16) with (e_S e + (-8 - 8 * Z.of_nat 1)) by (rewrite ES; lia).
  exact K1. }
(* the frame chain at the call *)
pose (ch := if spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)
            then [(spZ (h_regs rsegs hx), RA_LLVMF, s0Z (h_regs rsegs hx))] else []).
assert (KE : forall a, spZ (h_regs rsegs hx) <= a < 2 ^ 64 ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx) a).
{ intros a Ha. apply JK1; lia. }
assert (Hchain : achain lyc (aview rsegs (w_H W) memc) (e_R e) (spZ (h_regs rsegs hx)) ch).
{ apply (achain_ly_top (h_ly rsegs hx) lyc); [exact Etopc|]. unfold ch.
  destruct (Z.ltb_spec (spZ (h_regs rsegs hx) + 16) (ly_top (h_ly rsegs hx))) as [Hlt | Hge].
  - apply (achain_push (h_ly rsegs hx) (aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx)) (aview rsegs (w_H W) memc)
      (spZ (h_regs rsegs hx)) (s0Z (h_regs rsegs hx)) RA_LLVMF [] (e_R e) Hch0);
    [lia | exact KE | exact Hs8 | exact Hs16 | lia | lia | exact Hal8 | lia | lia].
  - left. split; [right; left; lia | reflexivity]. }
assert (Hch : chain_pre lyc (aview rsegs (w_H W) memc) regsT ch).
{ apply (achain_chain_pre lyc _ (e_R e) (spZ (h_regs rsegs hx)) ch regsT Hchain);
  [lia | exact Hs0T | rewrite HraT; unfold E01B_MALLOC_RA; lia]. }
assert (Htr : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B)).
{ apply (HTRACE regsT ch HraT). unfold ch.
  destruct (spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)); [right; do 2 eexists; reflexivity | left; reflexivity]. }
(* the budgets *)
assert (Hlive : blocks_bytes Sc + Layout.PP_SIZE <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), Eab, <- (blocks_bytes_bsum B (h_ly rsegs hx) (h_S rsegs hx)). lia. }
assert (Hev : st_nev Sc < EV_MAX) by lia.
assert (Hraw : YK0s.ret_ok (w64 E01B_MALLOC_RA)) by (apply ret_ok_even; vm_compute; reflexivity).
(* the call *)
unfold cfg_at. unfold E01B_MALLOC. rewrite <- HBmalloc.
eapply SRr_bind.
{ exact (aj_malloc_at04 rsegs B LAWS RPgSteps.rl_segs_low HAPI ML AMALLOC W regsT memc LLVMF_STK
    (spZ (h_regs rsegs hx)) [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx) (h_mem rsegs hx) (h_md rsegs hx)
    [(RH_CID, pos)] lyc Sc mdc 0 Layout.PP_SIZE (e_R e - spZ (h_regs rsegs hx)) (w64 E01B_MALLOC_RA) ch
    HJ Ha0 ltac:(unfold Layout.PP_SIZE, MALLOC_MAX; lia) Hlive ltac:(lia) HRo ltac:(lia) ltac:(lia)
    Hgp Htp Hra Hraw Hev Hch Htr). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec2 & HJ2 & Hpres & H10 & Hfrs2 & Hres & Eab2 & HK).
(* C1 *)
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
assert (EFa : frame_addr lyc RH_CID pos = e_F e) by (rewrite EF; unfold frame_addr; rewrite EFc; reflexivity).
assert (EFa2 : frame_addr ly2 RH_CID pos = e_F e) by (rewrite EF; unfold frame_addr; rewrite EF2; reflexivity).
assert (HinFc : In (RH_CID, pos) (frames Sc)) by (rewrite Hfrc; left; reflexivity).
assert (HinF2 : In (RH_CID, pos) (frames S2)) by (rewrite Hfrs2; exact HinFc).
assert (HinR : In (res, Layout.PP_SIZE) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
assert (Ereq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (Efs : fs_frame_bytes RH_CID = 1024) by reflexivity.
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 RH_CID pos HAR2 HinF2) as (HF1 & HF2 & _).
rewrite EFa2 in HF1. rewrite EFa2, Efs in HF2.
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 res Layout.PP_SIZE RH_CID pos HAR2 HinR HinF2) as HdRF.
rewrite EFa2, Efs, Ereq in HdRF. unfold zdisjoint in HdRF. cbn [fst snd] in HdRF.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res Layout.PP_SIZE HAR2 HinR) as (_ & _ & _ & HappR & _).
pose proof HK as (HK1 & HK2 & _ & HK4 & _).
assert (KS : forall a, e_R e <= a < 2 ^ 64 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha. apply HK1; lia. }
assert (KF : forall a, e_F e <= a < e_F e + 1024 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha. apply (HK4 RH_CID pos a HinFc).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, Efs. lia.
  - cbn beta. rewrite Ereq. lia. }
assert (KSh : forall i, 0 <= i < 128 ->
  aview rsegs (w_H W2) mem2 (shadow_addr (e_F e) + i) = aview rsegs (w_H W) memc (shadow_addr (e_F e) + i)).
{ intros i Hi. apply (HK4 RH_CID pos _ HinFc).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa, Efs. change (1024 / 8) with 128. lia.
  - cbn beta. exact (e01mb_sh_app (e_F e) i res (req_size Layout.PP_SIZE) HF1 HF2 Hi HappR). }
subst c2.
refine (HFROM pos (e01mb_env e res) rest ly2 S2 W2 regs2 mem2 md2 _).
unfold rh_cut_C1, rh_common.
split.
{ split; [exact HJ2|].
  split; [rewrite Hfrs2; exact Hfrc|].
  split; [rewrite Eab2, Eab; apply Permutation_refl|].
  split.
  { apply Forall_cons; [|apply Forall_nil].
    rewrite Eab in Eab2. exact (e01mb_fresh B ly2 S2 W2 mem2 md2 _ res HAR2 Eab2). }
  split; [exact (e01mb_pres regsT regs2 2 (e_R e) Hpres ltac:(unfold acallee_saved; lia) Hsp)|].
  split; [exact (e01mb_pres regsT regs2 3 (as_gp B) Hpres ltac:(unfold acallee_saved; lia) Hgp)|].
  split; [exact (e01mb_pres regsT regs2 4 (as_tp B) Hpres ltac:(unfold acallee_saved; lia) Htp)|].
  split; [exact Hgeo|].
  split; [exact Hhdr|].
  split; [exact Hhok|].
  split.
  { apply (e01mb_cut_call (w_H W) memc (w_H W2) mem2 regsT regs2 e res Hcut Hpres);
    [intros a Ha; apply KS; lia | exact H10]. }
  apply (e01mb_kept_call hx pos e res W memc regsT W2 mem2 regs2 Hkept).
  - intros j Hj i Hi. apply KS. lia.
  - intros i Hi. apply KF. lia. }
split; [cbn [e01mb_env e_pp]; lia|].
split.
{ apply (rm_fsh_kept rsegs (w_H W) memc); [exact Hfsh|]. intros i Hi.
  change (Z.of_nat (length (hi_shA role_himg_B))) with 88 in Hi. apply KSh. lia. }
apply (e01mb_input B hx W memc e rest ly2 S2 W2 mem2 md2 res Hin HAR2).
- rewrite Eab2, Eab. reflexivity.
- intros b m i Hb Hi Hn. apply (HK2 b m i); [rewrite Eab; exact Hb | exact Hi | exact Hn].
- intros p n Hp. pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 p n RH_CID pos HAR2 Hp HinF2) as D.
  rewrite EFa2, Efs in D. exact D.
- exact HRc.
- exact HF1.
- exact HF2.
Qed.
End b.
