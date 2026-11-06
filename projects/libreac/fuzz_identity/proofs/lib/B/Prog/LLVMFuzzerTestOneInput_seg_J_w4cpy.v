(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses changed; 647 of its 768 lines of code are new or changed and 5944 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan): the loop that appends the
   four width digits `w4` (SF+688) to the expected name `exp_nm` (SF+528) at offset ld, 0x81db8 .. 0x81dfc
   (BASE + 0x1644 .. BASE + 0x1688), to its join at 0x81e2c (BASE + 0x16b8).
   j_w4cpy_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v.

   The body (the neutral listing of fuzz_identity.asan-ubsan):
     0x81db8  add a6,s2,a0               a6 := &w4 + i
     0x81dbc  beq a6,a4 -> 0x82610       UBSan: &w4 + i is not -1
     0x81dc0  add a7,a1,a0               a7 := &exp_nm + ld + i
     0x81dc4  beqz a7 -> 0x82610         UBSan: &exp_nm + ld + i is not 0
     0x81dc8 .. 0x81dd4                  the ASan test of its shadow byte (slow path 0x81e04)
     0x81dd8  add a7,a2,a0 ; sb a5,0(a7) exp_nm[ld + i] := w4[i]
     0x81de0 .. 0x81df0                  the ASan test of the shadow byte of &w4 + 1 + i (slow path 0x81e10)
     0x81df4  lbu a5,1(a6) ; addi a0,a0,1
     0x81dfc  bnez a5 -> 0x81db8         the loop test; 0x81e00 j 0x81e20, 0x81e20 add s11,s11,a0
   One iteration (j_w4cpy_step) is one run of the token engine (IdentBPaLib.paj_run_tok) to the loop test, the
   branch on the next byte of `w4`, and one run back to the head or on to the join. The atom facts of the state
   decide the two UBSan traps; the two ASan tests are the engine's obligations, range_addressable of
   &exp_nm + ld + i and of &w4 + 1 + i, both inside a frame variable whose shadow is zero (sh_zero of the cut).
   The store's window is in the entry's own class-4 frame (own = [(4, pos)]), declared apart from the shadow
   band by an empty shadow entry (YCbq.shent_app_of_frame). The three computed addresses are atoms through the
   alias facts of the state (33 = &exp_nm + ld + i, 34 = &w4 + i). j_w4cpy_carry moves the cut's facts to the
   memory after the step (only exp_nm[ld + i] changed: it is below SF + 704, and every machine-stack slot the
   cut names is at or above mf >= SF + 688 + 16). The loop (j_w4cpy_loop) is an induction on the digits left,
   4 - i.

   Copied helpers (with this lemma's prefix; j_w4cpy_geo also states alloc_ceiling <= e_sp0 g <= 2 ^ 47): j_w4cpy_garr8_moved,
   j_w4cpy_garr8_snoc, j_w4cpy_zero_shadow_moved, j_w4cpy_block_shadow_moved, j_w4cpy_wvb_fds, j_w4cpy_wvb_fs, j_w4cpy_geo,
   j_w4cpy_chunk, j_w4cpy_U0, j_w4cpy_um1, j_w4cpy_nth_map, j_w4cpy_nth_end, j_w4cpy_nz, j_w4cpy_fits,
   j_w4cpy_tok_go_len and j_w4cpy_TK_len are the same-named helpers of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_dpcpy.v (which took them from
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v and lib/Prog/Seg/Tac_sh1.v); j_w4cpy_firstn_snoc is
   origin/main 2f680b0d9c66 proofs/tcpreplay/fuzz_services/lib/S1Strtol.v:62 firstn_S_app. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow addresses and the frame's alignment need it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at the loop head, 0x81db8 (BASE + 0x1644) ---------------------------------------- *)
(* Atoms: the registers; 32 = w4[i + 1] (the byte the iteration loads), 33 = &exp_nm + ld + i (the store
   address), 34 = &w4 + i (the source cursor). Region 0: the byte w4[i + 1], at offset 1 from the cursor,
   read-only. Region 1: the byte exp_nm[ld + i], base atom 33, writable. *)
Definition j_w4cpy_w4R : YP09.region := YP09.mkRegion (Some 34%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition j_w4cpy_nmR : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition j_w4cpy_atoms : list (nat * afact) :=
  [(6%nat, mkAF SB SB 0); (10%nat, mkAF 0 3 0); (11%nat, mkAF 4096 (2 ^ 47 - 16) 0);
   (12%nat, mkAF 4096 (2 ^ 47 - 16) 0); (13%nat, mkAF 4096 (2 ^ 47 - 16) 0);
   (14%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0); (15%nat, mkAF 1 255 0);
   (18%nat, mkAF 4096 (2 ^ 47 - 16) 0); (32%nat, mkAF 0 255 0);
   (33%nat, mkAF 4096 (2 ^ 47 - 16) 0); (34%nat, mkAF 4096 (2 ^ 47 - 16) 0)].
Definition j_w4cpy_ss : sstate :=
  mkSS 0x1644 sr_atoms [j_w4cpy_w4R; j_w4cpy_nmR] None
    (mkFacts j_w4cpy_atoms []
      [(SAlu ALU_ADD (SOff 18 0) (SOff 10 0), SOff 34 0);
       (SAlu ALU_ADD (SOff 11 0) (SOff 10 0), SOff 33 0);
       (SAlu ALU_ADD (SOff 12 0) (SOff 10 0), SOff 33 0);
       (SAlu ALU_ADD (SOff 13 0) (SOff 10 0), SOff 34 1)]).
(* The registers one iteration does not write. x27 is kept too, but only up to the exit slot, which adds the
   index to it, so it is asked for separately. *)
Definition j_w4cpy_KL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 11%bv; 12%bv; 13%bv; 14%bv; 18%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
   26%bv].
Definition j_w4cpy_KL27 : list (bv 5) := 27%bv :: j_w4cpy_KL.

(* ---- small lemmas -------------------------------------------------------------------------------------- *)
Section mv.
Variable segs : list Segment.
Lemma j_w4cpy_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma j_w4cpy_garr8_snoc : forall (m : word -> option byte) a l v,
  garr8 segs m a l -> val_mem segs m (a + Z.of_nat (length l)) 1 v -> 0 <= v < 256 -> garr8 segs m a (l ++ [v]).
Proof.
intros m a l v Hg Hv Hr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hl | Hge].
- rewrite app_nth1 by exact Hl. exact (Hg j Hl).
- assert (Ej : j = length l) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  split; [exact Hv | exact Hr].
Qed.
End mv.
Lemma j_w4cpy_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma j_w4cpy_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
Qed.
Lemma j_w4cpy_wvb_fds : forall (md : Model) mat, m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti]; reflexivity. Qed.
Lemma j_w4cpy_wvb_fs : forall (md : Model) mat, m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti]; reflexivity. Qed.
Lemma j_w4cpy_firstn_snoc : forall {A : Type} (l : list A) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l. induction l as [|x l IH]; intros n d Hn; cbn [length] in Hn; [lia|].
destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
Lemma j_w4cpy_nth_map : forall (L : list byte) n, (n < length L)%nat ->
  nth n (map (fun b : byte => bv_unsigned b) (L ++ [RcIdentModel.zb 0])) 0 = bv_unsigned (nth n L (RcIdentModel.zb 0)).
Proof.
induction L as [|x L IH]; intros n Hn; cbn [length] in Hn; [lia|].
destruct n as [|n]; [reflexivity|]. cbn [app map nth]. apply IH. lia.
Qed.
Lemma j_w4cpy_nth_end : forall (L : list byte),
  nth (length L) (map (fun b : byte => bv_unsigned b) (L ++ [RcIdentModel.zb 0])) 0 = 0.
Proof. induction L as [|x L IH]; [reflexivity|]. cbn [length app map nth]. exact IH. Qed.
Lemma j_w4cpy_nz : forall (L : list byte) n, (n < length L)%nat -> ~ In (RcIdentModel.zb 0) L ->
  bv_unsigned (nth n L (RcIdentModel.zb 0)) <> 0.
Proof.
intros L n Hn Hnz E. apply Hnz.
assert (Ex : nth n L (RcIdentModel.zb 0) = RcIdentModel.zb 0) by (apply bv_eq; rewrite E; reflexivity).
rewrite <- Ex at 1. apply nth_In. exact Hn.
Qed.
Lemma j_w4cpy_um1 : bv_unsigned (Z_to_bv 64 (-1)) = 2 ^ 64 - 1.
Proof. reflexivity. Qed.
Lemma j_w4cpy_U0 : forall E n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id. subst v.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. unfold M64. lia.
Qed.
Lemma j_w4cpy_sv_val : forall (E : env) (x : sv) (v : Z), U E x = v -> sv_denot E x = w64 v.
Proof. intros E x v H. unfold U in H. unfold w64. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma j_w4cpy_Uc : forall E n c v, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof. intros E n c v H Hv. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.
Lemma j_w4cpy_tok_go_len : forall l d,
  length (SlotModel.tok_go d l) = (length l - (if negb d && SlotModel.has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b r IH]; intros d.
- destruct d; reflexivity.
- cbn [SlotModel.tok_go]. change (SlotModel.has_dash (b :: r)) with ((RcIdentModel.bz b =? 45) || SlotModel.has_dash r).
  destruct d; cbn [negb andb].
  + cbn [length]. rewrite IH. cbn [negb andb]. lia.
  + destruct (Z.eqb_spec (RcIdentModel.bz b) 45) as [E|E]; cbn [orb].
    * rewrite IH. cbn [negb andb length]. lia.
    * cbn [length]. rewrite IH. cbn [negb andb]. destruct (SlotModel.has_dash r) eqn:Hr; [|lia].
      assert (length r >= 1)%nat by (destruct r; [discriminate|cbn; lia]). lia.
Qed.
Lemma j_w4cpy_TK_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof.
intros inp. unfold SlotModel.n_TK, SlotModel.TOK, SlotModel.n_lt, SlotModel.n_ln. rewrite j_w4cpy_tok_go_len.
cbn [negb andb]. destruct (SlotModel.has_dash (SlotModel.n_EXP_NM inp)) eqn:H; [|lia].
destruct (SlotModel.n_EXP_NM inp) as [|x r]; [discriminate|]. cbn [length]. lia.
Qed.
Lemma j_w4cpy_fits : forall inp, SlotModel.n_r inp = 0 ->
  SlotModel.n_ln inp < SlotModel.t_cap_name inp /\ SlotModel.n_lt inp < SlotModel.t_cap_tok inp /\
  SlotModel.n_ld inp < SlotModel.t_cap_disp inp.
Proof.
intros inp H. unfold SlotModel.n_r in H.
destruct (SlotModel.n_wok inp && SlotModel.n_fits inp) eqn:E; [|discriminate].
apply andb_prop in E as [_ E]. unfold SlotModel.n_fits in E.
apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
apply Z.ltb_lt in E1, E2, E3. auto.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).

(* The value of the chunk at offset off of region i of a symbolic state. *)
Lemma j_w4cpy_chunk : forall E ss ms i r off (n : N) e b v,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> base_val E (YP09.r_base r) = b ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (ms_mem ms) (b + off) (N.to_nat n) v.
Proof.
intros E ss ms i r off n e b v HS Hi Hb Hin He Hv Hn.
pose proof (st_ok_pi_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hc). rewrite Hb in Hc.
apply (val_of_chunk_ok SEGS E (ms_mem ms) b off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hc _ Hin).
Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v, of the boundary file and of the statement file, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).

(* The two cuts of j_w4cpy_stmt, by name. *)
Definition j_w4cpy_head (g : ectx) (pos mf nm tk dp ld i : Z) (pre : list byte) :
  alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 ld /\
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
SlotModel.n_wok (e_pl g) = true /\
length (SlotModel.n_W4 (e_pl g)) = 4%nat /\
~ In (RcIdentModel.zb 0) (SlotModel.n_W4 (e_pl g)) /\
1 <= ld /\ ld + 4 + 1 <= N_nm /\
0 <= i < 4 /\
Z.of_nat (length pre) = ld /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (pre ++ firstn (Z.to_nat i) (SlotModel.n_W4 (e_pl g))) /\
getr regs2 10 = w64 i /\
getr regs2 11 = w64 (SFa g pos + V_nm + ld) /\
getr regs2 12 = w64 (SFa g pos + V_nm + ld) /\
getr regs2 13 = w64 (SFa g pos + V_w4 + 1) /\
getr regs2 14 = w64 (-1) /\
getr regs2 15 = w64 (bv_unsigned (nth (Z.to_nat i) (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0))).
Definition j_w4cpy_exit (g : ectx) (pos mf nm tk dp ld : Z) (pre : list byte) :
  alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (ld + 4) /\
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (pre ++ SlotModel.n_W4 (e_pl g)).
(* Where one iteration ends: back at the head with one more digit, or at the join with all four. *)
Definition j_w4cpy_next (g : ectx) (pos mf nm tk dp ld i : Z) (pre : list byte) : world SEGS -> config -> Prop :=
fun W3 c3 =>
(i + 1 < 4 /\
 ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1644)
   (j_w4cpy_head g pos mf nm tk dp ld (i + 1) pre) W3 c3) \/
(i + 1 = 4 /\
 ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x16b8)
   (j_w4cpy_exit g pos mf nm tk dp ld pre) W3 c3).

Section d.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The geometry of the entry's own class-4 frame, from the journal. *)
Lemma j_w4cpy_geo : forall (g : ectx) pos k ly2 S2 (W2 : world SEGS) mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 k ->
  frames S2 = [(4, pos)] ->
  frame_addr ly2 4 pos = SFa g pos /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ SFa g pos mod 64 = 0 /\
  0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\
  (SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos) /\
  alloc_ceiling <= e_sp0 g /\ e_sp0 g <= 2 ^ 47.
Proof.
intros g pos k ly2 S2 W2 mem2 md2 HJ Hfrs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
split; [exact EFa|]. split; [exact HSF0|]. split; [exact HSF1|]. split; [exact HSF64|].
split; [clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia|].
split; [clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia|].
split.
{ clear - Esh HSF0 HSF1 HSFapp C1.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  destruct HSFapp as (_ & [Hlo | [Hhi1 Hhi2]]); [left | right]; lia. }
clear - Hstk0 Hceil Hslo Hshi H47. split; lia.
Qed.

(* ---- what one iteration keeps: every fact of the cut but exp_nm[ld + i], which now holds w4[i] ---------- *)
Lemma j_w4cpy_carry : forall (g : ectx) pos mf nm tk dp ld i (pre : list byte)
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3 k,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 k ->
  frames S2 = [(4, pos)] ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  j_w4cpy_head g pos mf nm tk dp ld i pre ly2 S2 W2 regs2 mem2 md2 ->
  (forall x, 0 <= x < 2 ^ 64 -> x <> SFa g pos + V_nm + ld + i ->
    aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W2) mem2 x) ->
  val_mem SEGS (rd W2 mem3) (SFa g pos + V_nm + ld + i) 1
    (bv_unsigned (nth (Z.to_nat i) (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0))) ->
  (forall r, In r j_w4cpy_KL -> getr regs3 r = getr regs2 r) ->
  m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
  ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3 /\ JKEEP g pos mf nm tk dp ly2 S2 W2 regs3 mem3 /\
  getr regs3 6 = w64 SHADOW_OFF /\
  getr regs3 11 = w64 (SFa g pos + V_nm + ld) /\ getr regs3 12 = w64 (SFa g pos + V_nm + ld) /\
  getr regs3 13 = w64 (SFa g pos + V_w4 + 1) /\ getr regs3 14 = w64 (-1) /\
  getr regs3 18 = w64 (SFa g pos + V_w4) /\ getr regs3 25 = w64 (SFa g pos + V_nm) /\
  getr regs3 26 = w64 (SFa g pos + V_dp) /\
  sh_zero W2 mem3 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem3 (SFa g pos + V_dp) N_dp /\
  sh_zero W2 mem3 (SFa g pos + V_w4) N_w4 /\
  bytes_at8 W2 mem3 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
  val_mem SEGS (rd W2 mem3) (mf + M_n2) 8 0 /\
  bytes_at8 W2 mem3 (SFa g pos + V_nm) (pre ++ firstn (Z.to_nat (i + 1)) (SlotModel.n_W4 (e_pl g))).
Proof.
intros g pos mf nm tk dp ld i pre ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 k HJ Hfrs HC HP KEEP Vnew RK Efds Efs.
destruct HP as (HK & R6 & R18 & R25 & R26 & R27 & R22 & Shnm & Shdp & Shw4 & Bw4 & Hwok & Hlen4 & Hnz &
  Hld1 & Hld2 & Hi & Hplen & Vn2 & Bnm & R10 & R11 & R12 & R13 & R14 & R15).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR2 & _).
destruct (j_w4cpy_geo g pos k ly2 S2 W2 mem2 md2 HJ Hfrs)
  as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh & Hceil & H47).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
set (SF := SFa g pos) in *.
set (L := SlotModel.n_W4 (e_pl g)) in *.
unfold N_nm in Hld2.
(* the arithmetic every address below needs, as one fact *)
assert (HA : 4096 <= SF /\ SF + 1024 <= alloc_ceiling /\ alloc_ceiling <= 2 ^ 47 /\ SF + 688 <= mf /\
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ e_sp0 g <= 2 ^ 47 /\ 0 <= i < 4 /\ 1 <= ld /\ ld + 5 <= 32)
  by (clear - HSF0 HSF1 C1 Hmfb Hceil H47 Hi Hld1 Hld2; lia).
clear Hmfb Hceil H47.
assert (VK : forall x (n : nat) v, 0 <= x -> x + Z.of_nat n <= 2 ^ 64 ->
  (x + Z.of_nat n <= SF + V_nm + ld + i \/ SF + V_nm + ld + i < x) ->
  val_mem SEGS (rd W2 mem2) x n v -> val_mem SEGS (rd W2 mem3) x n v).
{ intros x n v H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 x x n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H0 H1 H2 Hkk; lia. }
assert (GK : forall x l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= x + kk < 2 ^ 64 /\ x + kk <> SF + V_nm + ld + i) ->
  garr8 SEGS (rd W2 mem2) x l -> garr8 SEGS (rd W2 mem3) x l).
{ intros x l Hd Hg. apply (j_w4cpy_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 x l); [|exact Hg].
  intros kk Hkk. destruct (Hd kk Hkk) as [Ha Hne]. exact (KEEP (x + kk) Ha Hne). }
assert (SHK : forall off j, 0 <= off -> off mod 8 = 0 -> 0 <= off / 8 + j < 128 ->
  aview SEGS (w_H W2) mem3 (shadow_of_addr SHADOW_OFF (SF + off) + j) =
  aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF (SF + off) + j)).
{ intros off j H0 H8 Hj.
  replace (shadow_of_addr SHADOW_OFF (SF + off) + j) with (shadow_addr SF + (off / 8 + j))
    by (unfold shadow_of_addr, shadow_addr; clear - HSF64 H0 H8; Z.div_mod_to_equations; lia).
  apply KEEP; [clear - Hj Hsh0 Hsh1 HA; lia | clear - Hj Hsfsh HA; unfold V_nm; lia]. }
assert (ZS : forall off n, 0 <= off -> off mod 8 = 0 -> 0 <= n -> off + n <= 1024 ->
  sh_zero W2 mem2 (SF + off) n -> sh_zero W2 mem3 (SF + off) n).
{ intros off n H0 H8 Hn H1 Hz. unfold sh_zero in *.
  apply (j_w4cpy_zero_shadow_moved (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + off) n); [|exact Hz].
  intros j Hj. apply SHK; [exact H0 | exact H8 | clear - H0 H8 H1 Hn Hj; Z.div_mod_to_equations; lia]. }
assert (BS : forall off n, 0 <= off -> off mod 8 = 0 -> 0 <= n -> off + n <= 1024 ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W2 mem3 (SF + off) n).
{ intros off n H0 H8 Hn H1 Hz. unfold sh_blk in *.
  apply (j_w4cpy_block_shadow_moved (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + off) n); [|exact Hz].
  intros j Hj. apply SHK; [exact H0 | exact H8 | clear - H0 H8 H1 Hn Hj; Z.div_mod_to_equations; lia]. }
assert (BLK : forall b n l, In (b, n) (ablocks B ly2 S2) -> 0 <= n -> Z.of_nat (length l) <= n ->
  garr8 SEGS (rd W2 mem2) b l -> garr8 SEGS (rd W2 mem3) b l).
{ intros b n l Hin Hn Hlen' Hg. apply GK; [|exact Hg]. intros kk Hkk.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b n HAR2 Hin) as (_ & Hb4096 & Hbce & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b n 4 pos HAR2 Hin Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  pose proof (req_size_pos n Hn) as Hrq.
  split; [clear - Hkk Hlen' Hb4096 Hbce Hrq HA; lia | clear - Hkk Hlen' Hdf Hrq HA; unfold V_nm; lia]. }
destruct Hbl as [Hperm Hhs].
split.
{ (* ecommon *)
  unfold ecommon.
  split; [rewrite (RK 2%bv ltac:(cbn; tauto)); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(cbn; tauto)); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(cbn; tauto)); exact Rs0|].
  split; [clear - HA; lia|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact Rtp|].
  do 17 (split; [apply VK; [clear - HA; lia | clear - HA; lia | right; clear - HA; unfold V_nm; lia | assumption]|]).
  split; [apply VK; [clear - HA; lia | clear - HA; lia | right; clear - HA; unfold V_nm; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [rewrite Efds; exact Hfds|].
  split; [rewrite Efs; exact Hfs|].
  pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
  unfold bytes_at8 in Hinb |- *.
  destruct Hinp as [[Hn0 _] | [_ Hine]].
  - apply GK; [|exact Hinb]. intros kk Hkk. rewrite length_map in Hkk. clear - Hkk Hlen Hn0. lia.
  - apply (BLK (e_p g) (e_n g)); [| |rewrite length_map; clear - Hlen; lia | exact Hinb].
    + apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine.
    + clear - Hlen. lia. }
split.
{ (* jkeep *)
  unfold jkeep.
  split; [split; [exact Hperm | exact Hhs]|].
  split; [unfold sh_reg in *; rewrite (RK 23%bv ltac:(cbn; tauto)); exact Rs7|].
  split; [rewrite (RK 24%bv ltac:(cbn; tauto)); exact R24|].
  split; [rewrite (RK 21%bv ltac:(cbn; tauto)); exact R21|].
  do 8 (split; [apply VK; [clear - HA; lia | clear - HA; lia | right; clear - HA; unfold V_nm; lia | assumption]|]).
  split.
  { unfold id_at in *. destruct Hid as (Hidb & Hidz & Hidk). split; [|split].
    - unfold bytes_at8 in *. apply GK; [|exact Hidb]. intros kk Hkk. rewrite length_map in Hkk.
      unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk. unfold RcIdentModel.ID_SIZE in Hkk.
      unfold V_id, V_nm. split; clear - Hkk HA; lia.
    - apply ZS; [unfold V_id; clear; lia | reflexivity | unfold N_id; clear; lia | unfold V_id, N_id; clear; lia | exact Hidz].
    - apply BS; [unfold V_id; clear; lia | reflexivity | unfold N_id; clear; lia | unfold V_id, N_id; clear; lia | exact Hidk]. }
  intros Hr0. destruct (Hbufs Hr0) as (Bn & Bt & Bd).
  destruct (j_w4cpy_fits (e_pl g) Hr0) as (Fn & Ft & Fd).
  pose proof (j_w4cpy_TK_len (e_pl g)) as HTK.
  unfold bytes_at8 in *.
  split; [|split].
  - apply (BLK nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1)); [| | |exact Bn].
    + apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity.
    + clear. lia.
    + rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ln in Fn. clear - Fn. lia.
  - apply (BLK tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1)); [| | |exact Bt].
    + apply (Permutation_in _ (Permutation_sym Hperm)). right. left. reflexivity.
    + clear. lia.
    + rewrite length_map, length_app. cbn [length]. clear - Ft HTK. lia.
  - apply (BLK dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)); [| | |exact Bd].
    + apply (Permutation_in _ (Permutation_sym Hperm)). right. right. left. reflexivity.
    + clear. lia.
    + rewrite length_map, length_app. cbn [length]. unfold SlotModel.n_ld in Fd. clear - Fd. lia. }
split; [rewrite (RK 6%bv ltac:(cbn; tauto)); exact R6|].
split; [rewrite (RK 11%bv ltac:(cbn; tauto)); exact R11|].
split; [rewrite (RK 12%bv ltac:(cbn; tauto)); exact R12|].
split; [rewrite (RK 13%bv ltac:(cbn; tauto)); exact R13|].
split; [rewrite (RK 14%bv ltac:(cbn; tauto)); exact R14|].
split; [rewrite (RK 18%bv ltac:(cbn; tauto)); exact R18|].
split; [rewrite (RK 25%bv ltac:(cbn; tauto)); exact R25|].
split; [rewrite (RK 26%bv ltac:(cbn; tauto)); exact R26|].
split; [apply ZS; [unfold V_nm; clear; lia | reflexivity | unfold N_nm; clear; lia | unfold V_nm, N_nm; clear; lia | exact Shnm]|].
split; [apply ZS; [unfold V_dp; clear; lia | reflexivity | unfold N_dp; clear; lia | unfold V_dp, N_dp; clear; lia | exact Shdp]|].
split; [apply ZS; [unfold V_w4; clear; lia | reflexivity | unfold N_w4; clear; lia | unfold V_w4, N_w4; clear; lia | exact Shw4]|].
split.
{ unfold bytes_at8 in *. apply GK; [|exact Bw4]. intros kk Hkk.
  rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk. rewrite Hlen4 in Hkk.
  unfold V_nm, V_w4. split; clear - Hkk HA; lia. }
split; [apply VK; [clear - HA; unfold M_n2; lia | clear - HA; unfold M_n2; lia |
  right; clear - HA; unfold V_nm, M_n2; lia | exact Vn2]|].
(* exp_nm, with one more digit *)
unfold bytes_at8 in *.
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear - HA; lia).
rewrite (j_w4cpy_firstn_snoc L (Z.to_nat i) (RcIdentModel.zb 0)) by (clear - HA Hlen4; lia).
rewrite app_assoc, map_app. cbn [map].
pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) L (RcIdentModel.zb 0))) as Hbr.
change (bv_modulus 8) with 256 in Hbr.
assert (Hfl : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (pre ++ firstn (Z.to_nat i) L))) = ld + i)
  by (rewrite length_map, length_app, length_firstn, Hlen4; clear - HA Hplen; lia).
apply j_w4cpy_garr8_snoc;
  [| rewrite Hfl; replace (SF + V_nm + (ld + i)) with (SF + V_nm + ld + i) by (clear; lia); exact Vnew
   | clear - Hbr; lia].
apply GK; [|exact Bnm]. intros kk Hkk. rewrite Hfl in Hkk. unfold V_nm. split; clear - Hkk HA; lia.
Qed.

(* ---- one iteration, from the head to the head or to the join ------------------------------------------- *)
Lemma j_w4cpy_step : forall (g : ectx) pos mf nm tk dp ld i (pre : list byte) W2 c2,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1644)
    (j_w4cpy_head g pos mf nm tk dp ld i pre) W2 c2 ->
  SRr SEGS W2 c2 (j_w4cpy_next g pos mf nm tk dp ld i pre).
Proof.
intros g pos mf nm tk dp ld i pre W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
pose proof HP as (_ & R6 & R18 & R25 & R26 & R27 & R22 & Shnm & Shdp & Shw4 & Bw4 & Hwok & Hlen4 & Hnz &
  Hld1 & Hld2 & Hi & Hplen & Vn2 & Bnm & R10 & R11 & R12 & R13 & R14 & R15).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR2 & _).
destruct (j_w4cpy_geo g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs)
  as (EFa & HSF0 & HSF1 & HSF64 & _ & _ & _ & _ & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ as HJ0.
set (SF := SFa g pos) in *.
set (L := SlotModel.n_W4 (e_pl g)) in *.
unfold N_nm in Hld2.
assert (HA : 4096 <= SF /\ SF + 1024 <= alloc_ceiling /\ alloc_ceiling <= 2 ^ 47 /\
  0 <= i < 4 /\ 1 <= ld /\ ld + 5 <= 32 /\ length L = 4%nat)
  by (clear - HSF0 HSF1 C1 Hi Hld1 Hld2 Hlen4; repeat split; lia).
(* the byte the iteration stores and the byte it loads *)
set (b0 := bv_unsigned (nth (Z.to_nat i) L (RcIdentModel.zb 0))) in *.
assert (Hb0 : 1 <= b0 < 256).
{ pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) L (RcIdentModel.zb 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr.
  pose proof (j_w4cpy_nz L (Z.to_nat i) ltac:(clear - HA; lia) Hnz) as Hn0.
  unfold b0. clear - Hr Hn0. lia. }
set (b1 := nth (Z.to_nat (i + 1)) (map (fun b : byte => bv_unsigned b) (L ++ [RcIdentModel.zb 0])) 0).
assert (Vb1 : val_mem SEGS (rd W2 mem2) (SF + V_w4 + (i + 1)) 1 b1 /\ 0 <= b1 < 256).
{ unfold bytes_at8 in Bw4. apply (garr8_nthZ SEGS _ (SF + V_w4) _ (i + 1) Bw4); [clear - HA; lia|].
  rewrite length_map, length_app. cbn [length]. clear - HA. lia. }
destruct Vb1 as [Vb1 Hb1].
(* the shadow of the two variables *)
assert (RAnm : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (SF + V_nm) N_nm).
{ apply zero_shadow_range; [unfold V_nm; clear - HSF64; Z.div_mod_to_equations; lia | reflexivity | exact Shnm]. }
assert (RAw4 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (SF + V_w4) N_w4).
{ apply zero_shadow_range; [unfold V_w4; clear - HSF64; Z.div_mod_to_equations; lia | reflexivity | exact Shw4]. }
(* the environment: the registers, then atoms 32 = w4[i + 1], 33 = &exp_nm + ld + i, 34 = &w4 + i *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 b1; Z_to_bv 64 (SF + V_nm + ld + i); Z_to_bv 64 (SF + V_w4 + i)]))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn'; subst E; apply ew_Eimg_Ereg_nat; exact Hn').
assert (E32 : ew E 32 = Z_to_bv 64 b1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SF + V_nm + ld + i))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SF + V_w4 + i))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 b1; Z_to_bv 64 (SF + V_nm + ld + i); Z_to_bv 64 (SF + V_w4 + i)]) E)
  by (subst E; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; clear - Hn'; lia | reflexivity]).
assert (ER : regs_ok E sr_atoms regs2) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U6 : bv_unsigned (ew E 6) = SB).
{ rewrite (EE 6%nat 6%bv eq_refl), R6, SB_SHADOW_OFF. apply unsigned_lit_small. unfold SHADOW_OFF. clear. lia. }
assert (U10 : bv_unsigned (ew E 10) = i).
{ rewrite (EE 10%nat 10%bv eq_refl), R10. apply unsigned_lit_small. clear - HA. lia. }
assert (U11 : bv_unsigned (ew E 11) = SF + V_nm + ld).
{ rewrite (EE 11%nat 11%bv eq_refl), R11. apply unsigned_lit_small. unfold V_nm. clear - HA. lia. }
assert (U12 : bv_unsigned (ew E 12) = SF + V_nm + ld).
{ rewrite (EE 12%nat 12%bv eq_refl), R12. apply unsigned_lit_small. unfold V_nm. clear - HA. lia. }
assert (U13 : bv_unsigned (ew E 13) = SF + V_w4 + 1).
{ rewrite (EE 13%nat 13%bv eq_refl), R13. apply unsigned_lit_small. unfold V_w4. clear - HA. lia. }
assert (U14 : bv_unsigned (ew E 14) = 2 ^ 64 - 1).
{ rewrite (EE 14%nat 14%bv eq_refl), R14. exact j_w4cpy_um1. }
assert (U15 : bv_unsigned (ew E 15) = b0).
{ rewrite (EE 15%nat 15%bv eq_refl), R15. apply unsigned_lit_small. clear - Hb0. lia. }
assert (U18 : bv_unsigned (ew E 18) = SF + V_w4).
{ rewrite (EE 18%nat 18%bv eq_refl), R18. apply unsigned_lit_small. unfold V_w4. clear - HA. lia. }
assert (U27 : bv_unsigned (ew E 27) = ld).
{ rewrite (EE 27%nat 27%bv eq_refl), R27. apply unsigned_lit_small. clear - HA. lia. }
assert (U32 : bv_unsigned (ew E 32) = b1) by (rewrite E32; apply unsigned_lit_small; clear - Hb1; lia).
assert (U33 : bv_unsigned (ew E 33) = SF + V_nm + ld + i)
  by (rewrite E33; apply unsigned_lit_small; unfold V_nm; clear - HA; lia).
assert (U34 : bv_unsigned (ew E 34) = SF + V_w4 + i)
  by (rewrite E34; apply unsigned_lit_small; unfold V_w4; clear - HA; lia).
(* the symbolic state at the head *)
assert (HS : st_ok_pi SEGS VAL E j_w4cpy_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1644)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold j_w4cpy_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold j_w4cpy_w4R, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U34. split; [unfold V_w4; clear - HA; lia|]. split; [unfold V_w4; clear - HA; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (SF + V_w4 + i) 1 1 (SOff 32 0) b1);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | clear - Hb1; lia | clear; lia
      | replace (SF + V_w4 + i + 1) with (SF + V_w4 + (i + 1)) by (clear; lia); exact Vb1 ].
    + unfold j_w4cpy_nmR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [unfold V_nm; clear - HA; lia|]. split; [unfold V_nm; clear - HA; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (SF + V_nm + ld + i + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; unfold V_nm; clear - Ho HA; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, j_w4cpy_w4R, j_w4cpy_nmR. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U33, U34. right. unfold V_nm, V_w4. clear - HA. lia.
  - unfold facts_ok, j_w4cpy_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U6, U10, U11, U12, U13, U14, U15, U18, U32, U33, U34. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB, V_nm, V_w4. clear - HA Hb0 Hb1.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + assert (AL : forall (n m : nat) (c u v : Z), bv_unsigned (ew E n) = u -> bv_unsigned (ew E m) = v ->
        0 <= u -> u + i < 2 ^ 64 -> 0 <= v + c -> v + c < 2 ^ 64 -> u + i = v + c ->
        sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff 10 0)) = sv_denot E (SOff m c)).
      { intros n m c u v Hu Hv H1 H2 H3 H4 H5. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
        rewrite !U_SOff, Hu, Hv, U10, !Z.add_0_r. unfold zcanon, M64.
        rewrite !(Z.mod_small _ (2 ^ 64)) by (clear - H1 H2 H3 H4 HA; lia). exact H5. }
      split; [exact (AL 18%nat 34%nat 0 _ _ U18 U34 ltac:(unfold V_w4; clear - HA; lia)
        ltac:(unfold V_w4; clear - HA; lia) ltac:(unfold V_w4; clear - HA; lia)
        ltac:(unfold V_w4; clear - HA; lia) ltac:(clear; lia))|].
      split; [exact (AL 11%nat 33%nat 0 _ _ U11 U33 ltac:(unfold V_nm; clear - HA; lia)
        ltac:(unfold V_nm; clear - HA; lia) ltac:(unfold V_nm; clear - HA; lia)
        ltac:(unfold V_nm; clear - HA; lia) ltac:(clear; lia))|].
      split; [exact (AL 12%nat 33%nat 0 _ _ U12 U33 ltac:(unfold V_nm; clear - HA; lia)
        ltac:(unfold V_nm; clear - HA; lia) ltac:(unfold V_nm; clear - HA; lia)
        ltac:(unfold V_nm; clear - HA; lia) ltac:(clear; lia))|].
      split; [exact (AL 13%nat 34%nat 1 _ _ U13 U34 ltac:(unfold V_w4; clear - HA; lia)
        ltac:(unfold V_w4; clear - HA; lia) ltac:(unfold V_w4; clear - HA; lia)
        ltac:(unfold V_w4; clear - HA; lia) ltac:(clear; lia))|].
      exact I. }
assert (SHOK : sh_ok SEGS (SOff 6 0) [mkSHE 33 1 0] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (shent_app_of_frame SEGS B LAWS ly2 S2 W2 mem2 md2 E (SOff 6 0) 33%nat (SF + V_nm + ld + i) 4 pos 0 1
    (mrestrict (w_H W2) mem2) HAR2 Hin4).
  - rewrite (j_w4cpy_U0 E 6 SB U6). reflexivity.
  - exact (j_w4cpy_U0 E 33 _ U33).
  - rewrite EFa. unfold V_nm. clear - HA. lia.
  - clear. lia.
  - rewrite EFa, HFB. unfold V_nm. clear - HA. lia. }
unfold cfg_at. change (w64 (BASE + 0x1644)) with (Z_to_bv 64 (BASE + 0x1644)).
(* ---- run 1: the head to the loop test 0x81dfc (BASE + 0x1688) ---- *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ (* one of the two ASan tests: &w4 + 1 + i, or &exp_nm + ld + i *)
  first
  [ rewrite (j_w4cpy_Uc E 34%nat 1 _ U34 ltac:(unfold V_w4; clear - HA; lia));
    apply (obl_of_range SEGS _ mem2 E (SOff 6 0) (SF + V_w4 + i + 1) 1 (SF + V_w4) N_w4 RAw4);
    [rewrite (j_w4cpy_U0 E 6 SB U6); reflexivity | clear - HA; lia | unfold N_w4; clear - HA; lia]
  | rewrite (j_w4cpy_U0 E 33 _ U33);
    apply (obl_of_range SEGS _ mem2 E (SOff 6 0) (SF + V_nm + ld + i) 1 (SF + V_nm) N_nm RAnm);
    [rewrite (j_w4cpy_U0 E 6 SB U6); reflexivity | clear - HA; lia | unfold N_nm; clear - HA; lia] ]. }
{ (* the other one *)
  first
  [ rewrite (j_w4cpy_Uc E 34%nat 1 _ U34 ltac:(unfold V_w4; clear - HA; lia));
    apply (obl_of_range SEGS _ mem2 E (SOff 6 0) (SF + V_w4 + i + 1) 1 (SF + V_w4) N_w4 RAw4);
    [rewrite (j_w4cpy_U0 E 6 SB U6); reflexivity | clear - HA; lia | unfold N_w4; clear - HA; lia]
  | rewrite (j_w4cpy_U0 E 33 _ U33);
    apply (obl_of_range SEGS _ mem2 E (SOff 6 0) (SF + V_nm + ld + i) 1 (SF + V_nm) N_nm RAnm);
    [rewrite (j_w4cpy_U0 E 6 SB U6); reflexivity | clear - HA; lia | unfold N_nm; clear - HA; lia] ]. }
{ (* the write right: the byte exp_nm + ld + i of the entry's own frame *)
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0' ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0' bc ly own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (SF + V_nm + ld + i));
    [reflexivity | exact U33 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
  right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. unfold V_nm in Ha |- *. clear - Ha HA. lia. }
rename ms into ms1. rename HFr into HFr1. clear HF HG.
lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ => set (E1 := Ex) in * end.
assert (EK1 : forall n, (n < 512)%nat -> ew E1 n = ew E n).
{ intros n Hn'. unfold E1. rewrite !ew_ewset_other by (clear - Hn'; lia). reflexivity. }
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> x <> SF + V_nm + ld + i ->
  aview SEGS (w_H W2) (ms_mem ms1) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx Hne.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms1) (fun y => y = SF + V_nm + ld + i) HFr1); [|exact Hx|exact Hne].
  intros bb wlo whi aa Hin Hr. cbv beta. unfold j_w4cpy_ss, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [clear - Hr; lia | rewrite U33 in Hr; clear - Hr; lia]. }
clear HFr1.
assert (U33' : bv_unsigned (ew E1 33) = SF + V_nm + ld + i) by (rewrite EK1 by (clear; lia); exact U33).
(* ---- the loop test on w4[i + 1] ---- *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* w4[i + 1] <> 0: back to the head *)
  rewrite YI04.branch_ne_U, (j_w4cpy_U0 E1 32 b1 ltac:(rewrite EK1 by (clear; lia); exact U32)), U_SLit in Hc.
  change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hmore : i + 1 < 4).
  { destruct (Z.lt_ge_cases (i + 1) 4) as [Hl | Hg]; [exact Hl|]. exfalso. apply Hc.
    unfold b1. replace (Z.to_nat (i + 1)) with (length L) by (clear - HA Hg; lia). apply j_w4cpy_nth_end. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x1644.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0' ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0' bc ly own) end.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (SF + V_nm + ld + i));
      [reflexivity | exact U33' | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. unfold V_nm in Ha |- *. clear - Ha HA. lia. }
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> x <> SF + V_nm + ld + i ->
    aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x).
  { intros x Hx Hne. rewrite <- (KEEP1 x Hx Hne).
    apply (kept_of_frame E1 _ (w_H W2) (ms_mem ms1) (ms_mem ms) (fun y => y = SF + V_nm + ld + i) HFr);
      [|exact Hx|exact Hne].
    intros bb wlo whi aa Hin Hr. cbv beta. cbn in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    [clear - Hr; lia | rewrite U33' in Hr; clear - Hr; lia]. }
  assert (Vnew : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_nm + ld + i) 1 b0).
  { replace (SF + V_nm + ld + i) with (SF + V_nm + ld + i + 0) by (clear; lia).
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r := eval vm_compute in (nth 1 (ss_mem ssx) j_w4cpy_nmR) in
      exact (j_w4cpy_chunk Ex ssx msx 1 r 0 1 (SOff 15 0) (SF + V_nm + ld + i) b0 HS
        ltac:(vm_compute; reflexivity) ltac:(cbn [base_val YP09.r_base]; exact U33')
        ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
        ltac:(rewrite denot_lit_U, (j_w4cpy_U0 E1 15 b0 ltac:(rewrite EK1 by (clear; lia); exact U15)); reflexivity)
        ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; clear - Hb0; lia) ltac:(clear; lia)) end. }
  assert (HAE1 : env_agree 32 (Ereg regs2 [Z_to_bv 64 b1; Z_to_bv 64 (SF + V_nm + ld + i);
      Z_to_bv 64 (SF + V_w4 + i)]) E1).
  { destruct HAE as [HA1 HD]. split; [intros n Hn'; rewrite EK1 by (clear - Hn'; lia); apply HA1; exact Hn' | exact HD]. }
  assert (RK : forall r, In r j_w4cpy_KL27 -> getr (ms_regs ms) r = getr regs2 r).
  { pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ j_w4cpy_KL27 HS HAE1 ltac:(vm_compute; reflexivity)) as KK.
    cbn [ms_regs restrict] in KK. exact KK. }
  assert (RK' : forall r, In r j_w4cpy_KL -> getr (ms_regs ms) r = getr regs2 r)
    by (intros r Hr; apply RK; right; exact Hr).
  prreg HS (10%bv : bv 5) Q10. prreg HS (15%bv : bv 5) Q15.
  rewrite (EK1 10%nat ltac:(clear; lia)), U10 in Q10.
  rewrite (EK1 32%nat ltac:(clear; lia)), E32 in Q15.
  repeat rewrite wvb_collapse in HJ.
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- j_w4cpy_next _ _ _ _ _ _ _ _ _ _ (mkCfg _ ?mdx) => set (md3 := mdx) end.
  destruct (j_w4cpy_carry g pos mf nm tk dp ld i pre ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) md3 _
    HJ0 Hfrs HC HP KEEP Vnew RK' (j_w4cpy_wvb_fds _ _) (j_w4cpy_wvb_fs _ _))
    as (HC3 & HK3 & Q6 & Q11 & Q12 & Q13 & Q14 & Q18 & Q25 & Q26 & Shnm3 & Shdp3 & Shw43 & Bw43 & Vn23 & Bnm3).
  left. split; [exact Hmore|].
  unfold acut. exists ly2, S2, (ms_regs ms), (ms_mem ms), md3.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|].
  unfold j_w4cpy_head.
  split; [exact HK3|]. split; [exact Q6|]. split; [exact Q18|]. split; [exact Q25|]. split; [exact Q26|].
  split; [rewrite (RK 27%bv ltac:(cbn; tauto)); exact R27|].
  split; [rewrite (RK' 22%bv ltac:(cbn; tauto)); exact R22|].
  split; [exact Shnm3|]. split; [exact Shdp3|]. split; [exact Shw43|]. split; [exact Bw43|].
  split; [exact Hwok|]. split; [exact Hlen4|]. split; [exact Hnz|].
  split; [exact Hld1|]. split; [unfold N_nm; clear - Hld2; lia|].
  split; [clear - HA Hmore; lia|].
  split; [exact Hplen|]. split; [exact Vn23|]. split; [exact Bnm3|].
  split; [rewrite Q10; unfold w64; f_equal; clear; lia|].
  split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|]. split; [exact Q14|].
  rewrite Q15. unfold b1. rewrite j_w4cpy_nth_map by (clear - HA Hmore; lia). reflexivity.
- (* w4[i + 1] = 0: the join *)
  rewrite YI04.branch_ne_U, (j_w4cpy_U0 E1 32 b1 ltac:(rewrite EK1 by (clear; lia); exact U32)), U_SLit in Hc.
  change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hend : i + 1 = 4).
  { destruct (Z.lt_ge_cases (i + 1) 4) as [Hl | Hg]; [|clear - HA Hg; lia]. exfalso.
    unfold b1 in Hc. rewrite j_w4cpy_nth_map in Hc by (clear - HA Hl; lia).
    exact (j_w4cpy_nz L (Z.to_nat (i + 1)) ltac:(clear - HA Hl; lia) Hnz Hc). }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x16b8.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0' ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0' bc ly own) end.
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (SF + V_nm + ld + i));
      [reflexivity | exact U33' | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. unfold V_nm in Ha |- *. clear - Ha HA. lia. }
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> x <> SF + V_nm + ld + i ->
    aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W2) mem2 x).
  { intros x Hx Hne. rewrite <- (KEEP1 x Hx Hne).
    apply (kept_of_frame E1 _ (w_H W2) (ms_mem ms1) (ms_mem ms) (fun y => y = SF + V_nm + ld + i) HFr);
      [|exact Hx|exact Hne].
    intros bb wlo whi aa Hin Hr. cbv beta. cbn in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    [clear - Hr; lia | rewrite U33' in Hr; clear - Hr; lia]. }
  assert (Vnew : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_nm + ld + i) 1 b0).
  { replace (SF + V_nm + ld + i) with (SF + V_nm + ld + i + 0) by (clear; lia).
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r := eval vm_compute in (nth 1 (ss_mem ssx) j_w4cpy_nmR) in
      exact (j_w4cpy_chunk Ex ssx msx 1 r 0 1 (SOff 15 0) (SF + V_nm + ld + i) b0 HS
        ltac:(vm_compute; reflexivity) ltac:(cbn [base_val YP09.r_base]; exact U33')
        ltac:(cbn [YP09.r_chunks In]; left; reflexivity)
        ltac:(rewrite denot_lit_U, (j_w4cpy_U0 E1 15 b0 ltac:(rewrite EK1 by (clear; lia); exact U15)); reflexivity)
        ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; clear - Hb0; lia) ltac:(clear; lia)) end. }
  assert (HAE1 : env_agree 32 (Ereg regs2 [Z_to_bv 64 b1; Z_to_bv 64 (SF + V_nm + ld + i);
      Z_to_bv 64 (SF + V_w4 + i)]) E1).
  { destruct HAE as [HA1 HD]. split; [intros n Hn'; rewrite EK1 by (clear - Hn'; lia); apply HA1; exact Hn' | exact HD]. }
  assert (RK' : forall r, In r j_w4cpy_KL -> getr (ms_regs ms) r = getr regs2 r).
  { pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ j_w4cpy_KL HS HAE1 ltac:(vm_compute; reflexivity)) as KK.
    cbn [ms_regs restrict] in KK. exact KK. }
  assert (Q27 : getr (ms_regs ms) 27 = w64 (ld + 4)).
  { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ _ (27%bv : bv 5) HS) as Qr.
    cbn [ms_regs restrict] in Qr.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
      let v := eval vm_compute in (sr_get (ss_regs ssx) (27%bv : bv 5)) in
      change (sr_get (ss_regs ssx) (27%bv : bv 5)) with v in Qr end.
    rewrite Qr. apply j_w4cpy_sv_val. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff.
    rewrite (EK1 27%nat ltac:(clear; lia)), (EK1 10%nat ltac:(clear; lia)), U27, U10.
    unfold zcanon, M64. rewrite !(Z.mod_small _ (2 ^ 64)) by (clear - HA; lia). clear - Hend HA. lia. }
  repeat rewrite wvb_collapse in HJ.
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- j_w4cpy_next _ _ _ _ _ _ _ _ _ _ (mkCfg _ ?mdx) => set (md3 := mdx) end.
  destruct (j_w4cpy_carry g pos mf nm tk dp ld i pre ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) md3 _
    HJ0 Hfrs HC HP KEEP Vnew RK' (j_w4cpy_wvb_fds _ _) (j_w4cpy_wvb_fs _ _))
    as (HC3 & HK3 & Q6 & Q11 & Q12 & Q13 & Q14 & Q18 & Q25 & Q26 & Shnm3 & Shdp3 & Shw43 & Bw43 & Vn23 & Bnm3).
  right. split; [exact Hend|].
  unfold acut. exists ly2, S2, (ms_regs ms), (ms_mem ms), md3.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC3|].
  unfold j_w4cpy_exit.
  split; [exact HK3|]. split; [exact Q6|]. split; [exact Q18|]. split; [exact Q25|]. split; [exact Q26|].
  split; [exact Q27|]. split; [rewrite (RK' 22%bv ltac:(cbn; tauto)); exact R22|].
  split; [exact Shnm3|]. split; [exact Shdp3|]. split; [exact Vn23|].
  assert (EF4 : Z.to_nat (i + 1) = length L) by (clear - Hend Hlen4; lia).
  rewrite EF4, firstn_all in Bnm3. exact Bnm3.
Qed.

(* ---- the loop: an induction on the digits left --------------------------------------------------------- *)
Lemma j_w4cpy_loop : forall (n : nat) (g : ectx) pos mf nm tk dp ld i (pre : list byte) W2 c2,
  Z.of_nat n = 4 - i ->
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1644)
    (j_w4cpy_head g pos mf nm tk dp ld i pre) W2 c2 ->
  SRr SEGS W2 c2 (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x16b8)
    (j_w4cpy_exit g pos mf nm tk dp ld pre)).
Proof.
induction n as [|n IH]; intros g pos mf nm tk dp ld i pre W2 c2 Hn Hst.
- exfalso. destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & HP).
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). clear - Hn Hi. lia.
- eapply SRr_bind; [exact (j_w4cpy_step g pos mf nm tk dp ld i pre W2 c2 Hst)|].
  intros W3 c3 _ [[Hlt Hc3] | [Heq Hc3]].
  + apply (IH g pos mf nm tk dp ld (i + 1) pre W3 c3); [clear - Hn; lia | exact Hc3].
  + apply SRr_ret. exact Hc3.
Qed.
End d.

(* ---- the statement ------------------------------------------------------------------------------------- *)
Lemma j_w4cpy : j_w4cpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold j_w4cpy_stmt. intros LAWS g pos mf nm tk dp ld i pre W2 c2 Hst.
assert (Hi : 0 <= i < 4).
{ destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & HP).
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). exact Hi. }
apply (j_w4cpy_loop LAWS (Z.to_nat (4 - i)) g pos mf nm tk dp ld i pre W2 c2);
  [clear - Hi; lia | exact Hst].
Qed.

Check (j_w4cpy : j_w4cpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
End c.
End b.
End a.
Print Assumptions j_w4cpy.
