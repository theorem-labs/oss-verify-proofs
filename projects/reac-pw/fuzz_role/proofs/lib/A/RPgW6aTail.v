(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the block lemmas w6_tail2 /
   w6_tail3 of lib/A/RPgW6aBase.v, the common tail of ent_build's cases 2 and 3 (pod.h:301, pod.h:321-322) to the
   join J 0x8165c. Proves no function (kind: segment lemma).
     0x815e8  ld a0,0xf0(s1); addi a3,zero,4; sw a3,0(a0); j 0x8164c          (case 2: e.type = 4)
     0x8163c  ld a0,0xf0(s1); addi a3,zero,6; sw a3,0(a0); addi a3,zero,4    (case 3: e.type = 6)
     0x8164c  sw a3,4(a0); sw a2,8(a0); sd a1,0xf8(s1); 0x81658 mv s9,s8      -> J 0x8165c
   No instrumented check and no branch: one engine run from the case's pc to J.
   THE ENTRY STATE, over Ereg regs [F + 0xf0] (env slot 32 = the address of e):
     tl_rR  based at s1 = R (x9): the cells [R+0xf0, R+0x100). [R+0xf0] is the 8-byte chunk holding slot 32's atom
            (the premise val_mem (R+0xf0) 8 (F+0xf0)), so `ld a0,0xf0(s1)` leaves a0 = that atom. Its write window
            [R+0xf8, R+0x100) (in.n's cell) lies in the journal's stack window (w6_ctx: R + 0x1a0 <= sp0 and
            sp0 - STK <= R - T_SEG_STK): awr_ok_cons_stack_off.
     tl_rE  based at slot 32: the write window [0, 12) = e.type, e.size, e.body[0..4), inside the frame (3, pos) the
            harness owns (fs_frame_bytes 3 = 512): awr_ok_cons_gen + in_frames.
     facts: R in [2^46, 2^47] and F + 0xf0 in [4096, 2^47], both 16-aligned. The block reads no shadow (no shadow
     entry, no obligation), so the shadow span the write windows are checked against is empty: (0, 0).
   THE POST: the four stored values from the final state's chunks (tl_val_at), the registers outside [a0; a3; s9]
   from their atoms (regs_kept_of_st_ok), every byte outside w6_tail_wr from the run's frame. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgSteps RPgW6aBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the entry state ======================================== *)
Definition tl_rR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xf0 0x100 0xf8 0x100 [YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0))].
Definition tl_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0 12 0 12 [].
Definition tl_regions : smem := [tl_rR; tl_rE].
Definition tl_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition ss_tl (pc : Z) : sstate := mkSS pc sr_atoms tl_regions None tl_facts.
Definition tl_extra (F : Z) : list word := [Z_to_bv 64 (F + 0xf0)].
Definition tl_Bx : sv := SLit SHADOW_OFF.
Definition tl_Bspan : Z * Z := (0, 0).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== helpers ======================================== *)
(* byte k of a stored word is byte k of its low w bytes *)
Lemma tl_byte : forall v (w k : nat), (k < w)%nat -> (w <= 8)%nat ->
Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte v w k).
Proof.
intros v w k Hk Hw. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). change 256 with (2 ^ 8).
rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hi8|Hi8].
- rewrite !(Z.mod_pow2_bits_low _ 8 i) by lia. rewrite !Z.shiftr_spec by lia.
  rewrite (Z.mod_pow2_bits_low v 64) by lia. rewrite (Z.mod_pow2_bits_low v (8 * Z.of_nat w)) by lia. reflexivity.
- rewrite !(Z.mod_pow2_bits_high _ 8 i) by lia. reflexivity.
Qed.
(* a chunk CVal n e of a region holds the low n bytes of e's value *)
Lemma tl_val_of_chunk : forall E mem base off (n : N) e v,
YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal n e)) -> sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat ->
val_mem rsegs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
unfold YP09.byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal. apply tl_byte; lia.
Qed.
(* the stored value as the statement gives it (mod 2 ^ (8 n)) *)
Lemma tl_val_mod : forall mem a (n : nat) v M, 2 ^ (8 * Z.of_nat n) = M ->
val_mem rsegs mem a n v -> val_mem rsegs mem a n (v mod M).
Proof.
intros mem a n v M HM H k Hk. rewrite (H k Hk). subst M. unfold YO0f.le_byte.
rewrite Z.mod_mod; [reflexivity|]. apply Z.pow_nonzero; lia.
Qed.
(* a chunk of region i of a final state, at absolute address a *)
Lemma tl_val_at : forall E ss H ms i r off (n : N) e v b a,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
sv_denot E e = Z_to_bv 64 v -> (N.to_nat n <= 8)%nat -> a = b + off ->
val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss H ms i r off n e v b a HS Hi Hc Hb He Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (tl_val_of_chunk E _ b off n e v Hck He Hn).
Qed.
(* a register of a final state *)
Lemma tl_reg : forall E ss H ms (r : bv 5) e w,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w.
Proof. intros E ss H ms r e w HS He Hw. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), He. exact Hw. Qed.
Lemma tl_atom : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

(* the entry state is sound for the machine at either case's pc *)
Lemma tl_entry : forall pc (W : world rsegs) regs memc R F,
getr regs 9 = w64 R -> 2 ^ 46 <= R -> R + 0x100 <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= F -> F + 512 <= R -> F mod 32 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (F + 0xf0) ->
(forall a, R + 0xf8 <= a < R + 0x100 -> apresent (w_H W) memc a) ->
(forall a, F + 0xf0 <= a < F + 0xfc -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (tl_extra F)) (ss_tl pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc R F H9 HR0 HR1 HR16 HF0 HFR HF32 Hval HpR HpE.
rewrite restrict_mkst_fx.
assert (B9 : bv_unsigned (ew (Ereg regs (tl_extra F)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (tl_extra F)) 32 = Z_to_bv 64 (F + 0xf0)) by exact (ew_Ereg_extra regs (tl_extra F) 0).
assert (B32 : bv_unsigned (ew (Ereg regs (tl_extra F)) 32) = F + 0xf0)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (HE16 : (F + 0xf0) mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply (proj1 (Z.mod_divide F 32 ltac:(lia))) in HF32.
  destruct HF32 as [q Hq]. exists (2 * q + 15). lia. }
unfold ss_tl. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold tl_regions, tl_rR, tl_rE. constructor; [|constructor; [|constructor]].
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9.
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable rsegs). apply HpR. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0xf0 8 (SOff 32 0) (F + 0xf0)).
      -- apply bv_eq. rewrite denot_SOff, B32, Z.add_0_r. rewrite unsigned_lit_small by lia.
         apply zcanon_id. unfold M64. lia.
      -- change (8 * Z.of_N 8) with 64. lia.
      -- cbn. lia.
      -- exact Hval.
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B32.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply HpE. lia.
- unfold tl_regions, tl_rR, tl_rE. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B32.
  split; [split; [right; lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]]. cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite B9, B32. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Ltac tl_reg_tac HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in
  eapply (tl_reg _ ssf _ _ r e); [exact HS | vm_compute; reflexivity |] end.
Ltac tl_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* both cases at once: c3 picks the start pc and the type *)
Lemma w6_tail_all : forall c3, w6_tail_stmt B MT c3.
Proof using MTL LAWS.
intros c3. unfold w6_tail_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos n' v c'
  (HJ & HR16 & HRhi & HRlo & Hown & HF & Hrom) H9 Hcell H11 H12 H24.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF32 & _ & HFpres & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFpres, HF4096, HFceil.
change (fs_frame_bytes 3) with 512 in HFpres, HFceil.
assert (BR : 2 ^ 46 <= R /\ R + 0x100 <= 2 ^ 47 /\ F + 512 <= R) by lia.
destruct BR as (BR0 & BR1 & BR2).
assert (B9 : bv_unsigned (ew (Ereg regs (tl_extra F)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs (tl_extra F)) 32 = Z_to_bv 64 (F + 0xf0)) by exact (ew_Ereg_extra regs (tl_extra F) 0).
assert (B32 : bv_unsigned (ew (Ereg regs (tl_extra F)) 32) = F + 0xf0)
  by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs (tl_extra F)) (ss_tl (if c3 then W6_T3 else W6_T2))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (if c3 then W6_T3 else W6_T2)) memc (seg_rom rsegs)))).
{ apply (tl_entry _ W regs memc R F H9 BR0 BR1 HR16 HF4096 BR2 HF32 Hcell).
  - intros a Ha. apply Hpres. lia.
  - intros a Ha. apply (proj1 (HFpres a ltac:(lia))). }
assert (SHOK : sh_ok rsegs tl_Bx [] (Ereg regs (tl_extra F)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (tl_extra F)) (Ereg regs (tl_extra F))) by apply env_agree_refl.
destruct c3; cbv beta iota in HS |- *; unfold cfg_at;
(aj_run_to_tok w6_tbl_ok HS HJ SHOK tl_Bspan W6_J;
[ (* the write windows: [R+0xf8, R+0x100) in the stack window, e's 12 bytes in the frame (3, pos) *)
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [ reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (F + 0xf0));
  [ reflexivity | exact B32
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
    right; right; right; exists 3, pos; split; [exact Hown|]; left;
    unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 3) with 512; lia
  | apply awr_ok_nil ]
| (* the leaf at J *)
  lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ =>
    apply SRr_ret; unfold w6_post; exists lyc, Sc, (ms_regs ms), (ms_mem ms), md end;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs (tl_extra F) (w_H W) _ HS HAE); vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ intros a Ha Hn; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    intros (r & Hin & Hr); apply Hn; unfold w6_tail_wr; rewrite unsigned_lit_small in Hr by lia;
    cbn [ss_mem ss_tl tl_regions In] in Hin;
    destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val tl_rR tl_rE] in Hr;
    rewrite ?B9, ?B32 in Hr; first [left; lia | right; lia]
  | cbv beta ];
  split; [tl_reg_tac HS (10%bv : bv 5); apply bv_eq; rewrite denot_SOff, B32, Z.add_0_r; unfold w64;
          rewrite unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia|];
  split; [tl_reg_tac HS (13%bv : bv 5); reflexivity|];
  split; [tl_reg_tac HS (25%bv : bv 5); rewrite (tl_atom regs _ 24 24%bv eq_refl); exact H24|];
  split; [eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 0 4%N _ _ (F + 0xf0) _);
          [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]|];
  split; [eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 4 4%N _ _ (F + 0xf0) _);
          [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B32 | reflexivity | cbn; lia | lia]|];
  split; [apply (tl_val_mod _ _ 4 v (2 ^ 32)); [reflexivity|];
          eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 8 4%N _ v (F + 0xf0) _);
          [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B32
          | rewrite (tl_atom regs _ 12 12%bv eq_refl); exact H12 | cbn; lia | lia]|];
  apply (tl_val_mod _ _ 8 n' (2 ^ 64)); [reflexivity|];
  eapply (tl_val_at _ _ (w_H W) ms 0%nat _ 0xf8 8%N _ n' R _);
  [exact HS | reflexivity | tl_in | cbn [YP09.r_base base_val]; exact B9
  | rewrite (tl_atom regs _ 11 11%bv eq_refl); exact H11 | cbn; lia | lia] ]).
Qed.

Theorem w6_tail2 : w6_tail2_stmt B MT.
Proof using MTL LAWS. exact (w6_tail_all false). Qed.
Theorem w6_tail3 : w6_tail3_stmt B MT.
Proof using MTL LAWS. exact (w6_tail_all true). Qed.
End d.
End b.

Print Assumptions w6_tail2.
Print Assumptions w6_tail3.
