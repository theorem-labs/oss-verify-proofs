From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import memcpy_c memset_c same_c pj_parse_c pj_free_c PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_c check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_spec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_ran_out_c.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* Phase B of check_no_overread (#102 plain): from the first parse_noting call (0x13a04, ra 0x138b8) through the three
   readings (trees at sp + 0x70, sp + 0x38, sp; results r1 -> s4, r2 -> s6, r0 -> s3), each followed by its
   out_of_memory() test (lbu g_own_ran_out, then fuzz_alloc_ran_out: both 0, so no branch to the frees at 0x139a0;
   cno_guard1 .. cno_guard3) and, when the readings succeed, the two compare calls, to the first pj_free call
   (0x15c08, ra 0x139a8) with s5 = ran_out = 0.  parse_noting needs g_ran_out = 0 at each call (its #102 contract):
   the first from the entry premise through the frame invariant cj (cno_cj_gro), the next two from the post of the
   reading before. *)

Ltac cnoB_ret := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Ltac cnoB_keepR :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

Section Ph.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x178d8.
Hypothesis HFREE : ms_free B = 0x17798.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.
Hypothesis RD0 : rd_cells B mem0.
Hypothesis HTP : ms_tp B = strtod_c.STRTOD_TP.
Hypothesis HERR : errno_addr B = strtod_c.STRTOD_ERRNO.
Hypothesis HGG : ms_got_guard B = strtod_c.STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = strtod_c.STRTOD_GUARD.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : strtod_c.STRTOD_GLOBALS_TOP <= spZ regs0 - CNO_K.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (data : Z) (x : list byte).
Hypothesis LED0 : ledger B L0 A0 mem0 Lam peak cnt (2 ^ 64 - 1).
Hypothesis CNT0 : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis XLEN : Z.of_nat (length x) <= 0x300000.
Hypothesis XB : Mem.bytes_at (ms_segs B) mem0 data x.
Hypothesis XBLK : x <> [] -> exists a k, In (a, k) (blocks L0 A0) /\ a <= data /\ data + Z.of_nat (length x) <= a + k.
Hypothesis ROOM : cno_room F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x).
Hypothesis FAR : fuzz_alloc_ran_out_contract.
Hypothesis GRO0 : Mem.bytes_at (ms_segs B) mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Hypothesis OWN0 : Mem.bytes_at (ms_segs B) mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).

Let J := cj B API L0 A0 regs0 mem0 md0.

Local Notation nx := (Z.of_nat (length x)).
Local Notation nc := (Z.of_nat (ncalls jr_strtod (zb x))).
Local Notation ct3 := (cnt + 3 * Z.of_nat (ncalls jr_strtod (zb x))).
Local Notation trx := (cno_tr x).
Local Notation ux := (cno_tv (json_read jr_strtod (zb x))).

(* The bound one parse leaves, and the list of the tree it builds, uniform over the parse outcome. *)
Definition cnoB_nb (bnd : rf_R F) (E : list (Z * Z)) : rf_R F :=
  match json_read jr_strtod (zb x) with
  | Some _ => rf_run F bnd (cno_tr x)
  | None => rf_frees F (rf_run F bnd (cno_tr x)) E
  end.

Definition cnoB_dt (D : list (Z * Z)) : Prop :=
  match json_read jr_strtod (zb x) with Some _ => cno_dl (cno_tr x) D | None => D = [] end.

(* The registers phase B keeps: sp, gp, tp, s0 = one, s1 = two, s2 = nul, s3 = n, s7 = 0x347b8, s8..s11. *)
Definition cnoB_R (regs : bvmap 5 word) (one two nul : Z) : Prop :=
  spZ regs = spZ regs0 - 240 /\ YK11.getr regs 3 = YK11.getr regs0 3 /\ YK11.getr regs 4 = YK11.getr regs0 4 /\
  YK11.getr regs 8 = Z_to_bv 64 one /\ YK11.getr regs 9 = Z_to_bv 64 two /\ YK11.getr regs 18 = Z_to_bv 64 nul /\
  YK11.getr regs 19 = Z_to_bv 64 nx /\ YK11.getr regs 23 = Z_to_bv 64 0x347b8 /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).

Definition cnoB_keep (regs regs' : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ 24 <= r <= 27) ->
    YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).

Lemma cnoB_num : 10096 <= CNO_K /\ YM05.alloc_ceiling + CNO_K <= spZ regs0 /\ spZ regs0 < 2 ^ 63 /\
  140735332483072 <= YM05.alloc_ceiling.
Proof.
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & H63 & _). pose proof cno_k_le. pose proof YM05.alloc_ceiling_value.
  split; [lia|]. split; [exact HK|]. split; [exact H63|]. lia.
Qed.

Lemma cnoB_al : (spZ regs0 - 240) mod 8 = 0 /\ (spZ regs0 - 240 + 56) mod 8 = 0 /\
  (spZ regs0 - 240 + 112) mod 8 = 0.
Proof.
  pose proof PRE0 as (_ & _ & _ & _ & H16 & _). clear -H16.
  split; [|split]; Z.div_mod_to_equations; lia.
Qed.

Lemma cnoB_nc : Z.of_nat (ncalls jr_strtod (zb x)) <= 2 * nx + 2.
Proof.
  assert (NC : (ncalls jr_strtod (zb x) <= 2 * length (zb x) + 2)%nat) by apply G7_4.
  assert (EL : length (zb x) = length x) by (unfold zb; apply length_map).
  rewrite EL in NC. lia.
Qed.

Lemma cnoB_saved_len : length (cno_saved regs0) = 72%nat.
Proof. unfold cno_saved. rewrite !length_app, !Mem.length_le8. reflexivity. Qed.

Lemma cnoB_depth : (depth ux <= 32)%nat.
Proof.
  unfold cno_tv. destruct (json_read jr_strtod (zb x)) as [t|] eqn:E.
  - pose proof (json_read_depth jr_strtod (zb x) t E) as H. unfold MAXD in H. exact H.
  - cbn [depth]. lia.
Qed.

Lemma cnoB_samek : 0 <= same_k ux <= 2640.
Proof. pose proof cnoB_depth as H. unfold same_k, SAME_FS. lia. Qed.

Lemma cnoB_case : cno_rv x = 0 \/ cno_rv x = -1.
Proof. unfold cno_rv. destruct (json_read jr_strtod (zb x)); [left | right]; reflexivity. Qed.

Lemma cnoB_pf : forall (A' : astate) bnd D,
  match json_read jr_strtod (zb x) with
  | Some _ => cno_dl (cno_tr x) D /\ rf_ok F A' (rf_run F bnd (cno_tr x))
  | None => D = [] /\ exists E, cno_dl (cno_tr x) E /\ rf_ok F A' (rf_frees F (rf_run F bnd (cno_tr x)) E)
  end ->
  exists E, cno_dl trx E /\ rf_ok F A' (cnoB_nb bnd E) /\ cnoB_dt D.
Proof.
  intros A' bnd D. unfold cnoB_nb, cnoB_dt. destruct (json_read jr_strtod (zb x)).
  - intros (H1 & H2). exists D. split; [exact H1|]. split; [exact H2 | exact H1].
  - intros (H1 & E & H2 & H3). exists E. split; [exact H2|]. split; [exact H3 | exact H1].
Qed.

Lemma cnoB_room2 : forall E1, cno_dl trx E1 -> room_run F (cnoB_nb (cno_b3 F b nx) E1) trx.
Proof.
  intros E1 H1. pose proof ROOM as (_ & _ & _ & _ & R). revert R.
  unfold cnoB_nb, cno_ok. destruct (json_read jr_strtod (zb x)); intros R.
  - exact (proj1 R).
  - exact (proj1 (R E1 H1)).
Qed.

Lemma cnoB_room3 : forall E1 E2, cno_dl trx E1 -> cno_dl trx E2 ->
  room_run F (cnoB_nb (cnoB_nb (cno_b3 F b nx) E1) E2) trx.
Proof.
  intros E1 E2 H1 H2. pose proof ROOM as (_ & _ & _ & _ & R). revert R.
  unfold cnoB_nb, cno_ok. destruct (json_read jr_strtod (zb x)); intros R.
  - exact (proj2 R).
  - exact (proj2 (R E1 H1) E2 H2).
Qed.

Lemma cnoB_bridge : forall E1 E2 E3 D1 D2 D0, cno_dl trx E1 -> cno_dl trx E2 -> cno_dl trx E3 ->
  cnoB_dt D1 -> cnoB_dt D2 -> cnoB_dt D0 ->
  forall D1' D2' D3', Permutation D1 D1' -> Permutation D2 D2' -> Permutation D0 D3' ->
    exists E1' E2' E3', cno_dl trx E1' /\ cno_dl trx E2' /\ cno_dl trx E3' /\
      rf_frees F (rf_frees F (rf_frees F (cnoB_nb (cnoB_nb (cnoB_nb (cno_b3 F b nx) E1) E2) E3) D1') D2') D3' =
      cno_mid F b nx trx (cno_ok x) E1' E2' E3'.
Proof.
  intros E1 E2 E3 D1 D2 D0 L1 L2 L3 T1 T2 T0 D1' D2' D3' P1 P2 P0. revert T1 T2 T0.
  unfold cnoB_dt, cnoB_nb, cno_ok, cno_mid. destruct (json_read jr_strtod (zb x)); intros T1 T2 T0.
  - exists D1', D2', D3'.
    split; [exact (cno_dl_perm _ _ _ P1 T1)|]. split; [exact (cno_dl_perm _ _ _ P2 T2)|].
    split; [exact (cno_dl_perm _ _ _ P0 T0)|]. reflexivity.
  - subst D1 D2 D0. apply Permutation_nil in P1, P2, P0. subst D1' D2' D3'.
    exists E1, E2, E3. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. reflexivity.
Qed.

Lemma cnoB_R_rp : forall regs regs' one two nul, cnoB_R regs one two nul -> regs_preserved regs regs' ->
  cnoB_R regs' one two nul.
Proof.
  intros regs regs' one two nul (Hs & H3 & H4 & H8 & H9 & H18 & H19 & H23 & H24) RP.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (RP 2); unfold callee_saved; lia|].
  split; [rewrite <- H3; apply (RP 3); unfold callee_saved; lia|].
  split; [rewrite <- H4; apply (RP 4); unfold callee_saved; lia|].
  split; [rewrite <- H8; apply (RP 8); unfold callee_saved; lia|].
  split; [rewrite <- H9; apply (RP 9); unfold callee_saved; lia|].
  split; [rewrite <- H18; apply (RP 18); unfold callee_saved; lia|].
  split; [rewrite <- H19; apply (RP 19); unfold callee_saved; lia|].
  split; [rewrite <- H23; apply (RP 23); unfold callee_saved; lia|].
  intros r Hr. rewrite <- (H24 r Hr). apply RP. unfold callee_saved. lia.
Qed.

Lemma cnoB_fin : forall regs regs' one two nul, cnoB_R regs one two nul -> cnoB_keep regs regs' ->
  spZ regs' = spZ regs0 - 240 /\ YK11.getr regs' 3 = YK11.getr regs0 3 /\ YK11.getr regs' 4 = YK11.getr regs0 4 /\
  YK11.getr regs' 8 = Z_to_bv 64 one /\ YK11.getr regs' 9 = Z_to_bv 64 two /\ YK11.getr regs' 18 = Z_to_bv 64 nul /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).
Proof.
  intros regs regs' one two nul (Hs & H3 & H4 & H8 & H9 & H18 & _ & _ & H24) K.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (K 2); lia|].
  split; [rewrite <- H3; apply (K 3); lia|].
  split; [rewrite <- H4; apply (K 4); lia|].
  split; [rewrite <- H8; apply (K 8); lia|].
  split; [rewrite <- H9; apply (K 9); lia|].
  split; [rewrite <- H18; apply (K 18); lia|].
  intros r Hr. rewrite <- (H24 r Hr). apply K. lia.
Qed.

Lemma cnoB_keep_trans : forall regs1 regs2 regs3, cnoB_keep regs1 regs2 -> cnoB_keep regs2 regs3 -> cnoB_keep regs1 regs3.
Proof. intros regs1 regs2 regs3 K1 K2 r Hr. rewrite (K2 r Hr). exact (K1 r Hr). Qed.

Lemma cnoB_R_jump : forall regs regs' R one two nul, cnoB_R regs one two nul ->
  (forall r, YK11.getr regs' r = YK11.getr R r) -> cnoB_keep regs R -> YK11.getr R 19 = YK11.getr regs 19 ->
  YK11.getr R 23 = Z_to_bv 64 0x347b8 ->
  cnoB_R regs' one two nul.
Proof.
  intros regs regs' R one two nul HR HGr K K19 K23.
  assert (K' : cnoB_keep regs regs') by (intros r Hr; rewrite HGr; exact (K r Hr)).
  destruct (cnoB_fin regs regs' one two nul HR K') as (Hs & H3 & H4 & H8 & H9 & H18 & H24).
  destruct HR as (_ & _ & _ & _ & _ & _ & H19 & _).
  split; [exact Hs|]. split; [exact H3|]. split; [exact H4|]. split; [exact H8|]. split; [exact H9|].
  split; [exact H18|]. split; [rewrite HGr, K19; exact H19|]. split; [rewrite HGr; exact K23 | exact H24].
Qed.

Lemma cnoB_noLam0 : forall q, ~ In (q, nx + 16) (blocks L0 A0) -> ~ In (q + 16, nx) Lam.
Proof.
  intros q Hq Hin. pose proof LED0 as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
  destruct (FA _ Hin) as (_ & HinB & _). cbn [fst snd] in HinB.
  replace (q + 16 - 16) with q in HinB by lia. exact (Hq HinB).
Qed.

Lemma cnoB_noLam {L A Lam' D Lam'' q} : Permutation Lam'' (D ++ Lam') -> new_blks L A D ->
  In (q, nx + 16) (blocks L A) -> ~ In (q + 16, nx) Lam' -> ~ In (q + 16, nx) Lam''.
Proof.
  intros HP ND Hq HL Hin. apply (Permutation_in _ HP) in Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|exact (HL Hin)].
  apply (ND _ _ Hin). replace (q + 16 - 16) with q by lia. exact Hq.
Qed.

Lemma cnoB_newD {L A m md D one two nul} : J L A m md -> new_blks L A D ->
  In (one, nx + 16) (blocks L A) -> In (two, nx + 16) (blocks L A) -> In (nul, nx + 16) (blocks L A) ->
  forall a k, In (a, k) D -> ~ In (a - 16, k + 16) (blocks L0 A0) /\ (a - 16, k + 16) <> (one, nx + 16) /\
    (a - 16, k + 16) <> (two, nx + 16) /\ (a - 16, k + 16) <> (nul, nx + 16).
Proof.
  intros HJ ND H1 H2 H3 a k Hin. pose proof (ND a k Hin) as Hn.
  split; [intros H0; exact (Hn (cj_blocks0 B API L0 A0 regs0 mem0 md0 L A m md _ _ HJ H0))|].
  split; [intros E; rewrite E in Hn; exact (Hn H1)|].
  split; [intros E; rewrite E in Hn; exact (Hn H2)|].
  intros E; rewrite E in Hn; exact (Hn H3).
Qed.

Lemma cnoB_ub {K L A regs m md E L' A' regs' m' md' q k a} :
  rpost B API K L A regs m md E (fun _ _ => False) L' A' regs' m' md' ->
  In (q, k) (user_blocks A) -> ptr_addr L q = a ->
  In (q, k) (user_blocks A') /\ ptr_addr L' q = a /\ In (a, k) (blocks L' A').
Proof.
  intros RP Hq Hp. destruct RP as (_ & _ & _ & _ & _ & _ & _ & SURV & PTR & _).
  pose proof (SURV q k Hq (fun H => H)) as Hq'. pose proof (PTR q k Hq Hq') as Ep.
  split; [exact Hq'|]. split; [congruence|]. rewrite <- Hp, <- Ep. exact (cno_ub_blocks L' A' q k Hq').
Qed.

Lemma cnoB_rp {K L A regs m md E g L' A' regs' m' md'} :
  rpost B API K L A regs m md E g L' A' regs' m' md' -> regs_preserved regs regs'.
Proof. intros RP. destruct RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _). exact RPr. Qed.

Lemma cnoB_ini {K L A regs m md E g L' A' regs' m' md'} :
  rpost B API K L A regs m md E g L' A' regs' m' md' -> st_init_done A = true -> st_init_done A' = true.
Proof. intros RP H. destruct RP as (_ & _ & _ & _ & HI & _). exact (HI H). Qed.

(* A copy block keeps its text across a reading (parse_noting writes only its tree and the allocator statics). *)
Lemma cnoB_bytes {L A regs m md L' A' regs' m' md' out} q a : J L A m md ->
  rpost B API PN_K L A regs m md (parse_noting_writes out) (fun _ _ => False) L' A' regs' m' md' ->
  spZ regs0 - 240 <= out -> In (q, nx + 16) (user_blocks A) -> ptr_addr L q = a ->
  Mem.bytes_at (ms_segs B) m a x -> Mem.bytes_at (ms_segs B) m' a x.
Proof.
  intros HJ RP Ho Hq Hp HB. pose proof HJ as (HM & _). pose proof cnoB_num as (HKv & HK & H63 & Hac).
  subst a. pose proof (cno_ub_blocks L A q _ Hq) as HqB.
  rewrite HS in HB |- *.
  refine (proj2 (proj2 (cno_blk_rpost B API HS L A regs m md PN_K (parse_noting_writes out) (fun _ _ => False)
    L' A' regs' m' md' q (nx + 16) x RP HB Hq (fun H => H) ltac:(lia) _))).
  intros i Hi [Hw|Hs].
  - destruct (cno_block_facts B API AX L A m md _ (nx + 16) i HM HqB ltac:(lia)) as (_ & _ & Hc & _). lia.
  - destruct (cno_block_facts B API AX L A m md _ (nx + 16) i HM HqB ltac:(lia)) as (_ & _ & _ & _ & Hni).
    exact (Hni (proj1 (cno_statics_free B API HG _ Hs))).
Qed.

Lemma cnoB_saved {L A regs m md L' A' regs' m' md' out} :
  rpost B API PN_K L A regs m md (parse_noting_writes out) (fun _ _ => False) L' A' regs' m' md' ->
  spZ regs = spZ regs0 - 240 -> out + 56 <= spZ regs0 - 72 ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) -> bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0).
Proof.
  intros RP Hsp Ho HB. pose proof cnoB_num as (HKv & HK & H63 & Hac).
  apply (cno_hi_rpost B API HS L A regs m md PN_K _ _ L' A' regs' m' md' _ _ RP HB); [lia|].
  rewrite cnoB_saved_len. intros i Hi. split.
  - unfold scratch_k. rewrite HERR. unfold strtod_c.STRTOD_ERRNO. lia.
  - intros [Hw|Hs]; [lia|].
    destruct (cno_statics_free B API HG _ Hs) as (_ & Hl & _). lia.
Qed.

Lemma cnoB_node {L A regs m md L' A' regs' m' md' out Lam1 Lam2 D' pk ct fl p t D} : J L A m md ->
  rpost B API PN_K L A regs m md (parse_noting_writes out) (fun _ _ => False) L' A' regs' m' md' ->
  ledger B L A m Lam1 pk ct fl -> pj_node (ms_segs B) m (lin Lam1) p t D -> Permutation Lam2 (D' ++ Lam1) ->
  spZ regs = spZ regs0 - 240 -> spZ regs0 - 240 <= out ->
  spZ regs0 - 240 <= p -> p + 56 <= spZ regs0 ->
  (p + 56 <= out \/ out + 56 <= p) ->
  pj_node (ms_segs B) m' (lin Lam2) p t D.
Proof.
  intros HJ RP HL HN HP Hsp Ho Hp1 Hp2 Hpo. pose proof HJ as (HM & _).
  pose proof cnoB_num as (HKv & HK & H63 & Hac).
  assert (HinL : forall a k, In (a, k) D -> In (a, k) Lam1) by exact (pj_node_blocks _ t m (lin Lam1) p D HN).
  apply (cno_tree_rpost B API HS L A regs m md PN_K _ _ L' A' regs' m' md' Lam1 Lam2 pk ct fl p t D RP HL HN).
  - intros a k Hin. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact (HinL a k Hin).
  - lia.
  - lia.
  - intros i Hi. split.
    + unfold scratch_k. rewrite HERR. unfold strtod_c.STRTOD_ERRNO. lia.
    + intros [Hw|Hs]; [lia|].
      destruct (cno_statics_free B API HG _ Hs) as (_ & Hl & _). lia.
  - intros a k Hin. split; [intros []|]. intros i Hi [Hw|Hs].
    + destruct (ledger_block_range B API L A m md Lam1 pk ct fl a k HM HL (HinL a k Hin)) as (R1 & R2 & R3). lia.
    + pose proof HL as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
      destruct (FA (a, k) (HinL a k Hin)) as (_ & _ & _ & HNI). cbn [fst snd] in HNI.
      apply (HNI (i + 16)); [lia|]. replace (a - 16 + (i + 16)) with (a + i) by lia.
      exact (proj1 (cno_statics_free B API HG _ Hs)).
Qed.

Lemma cnoB_foot {L A m md Lam' pk ct fl p t D} : J L A m md -> ledger B L A m Lam' pk ct fl ->
  pj_node (ms_segs B) m (lin Lam') p t D -> spZ regs0 - 240 <= p -> p + 56 <= spZ regs0 ->
  forall z, pj_foot p D z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
    outside [(spZ regs0 - 240 - same_k ux, spZ regs0 - 240)] z.
Proof.
  intros HJ HL HN Hp1 Hp2 z Hz. pose proof HJ as (HM & _). pose proof cnoB_num as (HKv & HK & H63 & Hac).
  pose proof cnoB_samek as SK.
  destruct (cno_foot B API HS L A m md Lam' pk ct fl p t D HM HL HN ltac:(lia) ltac:(lia) z Hz) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. cbn [outside]. split; [lia | exact I].
Qed.

Lemma cnoB_stk : forall L A m md lo, J L A m md -> spZ regs0 - CNO_K <= lo -> lo <= spZ regs0 - 240 ->
  stk rsegs (normalize rsegs m) lo (spZ regs0 - 240).
Proof.
  intros L A m md lo HJ Hlo Hlo2. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  pose proof cnoB_num as (HKv & HK & H63 & Hac).
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (cno_img_low B HS a Hi); lia).
  assert (W : writable_at (ms_segs B) m a) by (apply HSC; left; lia).
  destruct (cno_present_of_writable B HS m a ltac:(lia) Hni W) as [v Hv].
  pose proof (cno_ro_false B HS a ltac:(lia) Hni) as Hro.
  unfold wa, wview, mrd, normalize. rewrite Hro, Hv. cbv beta iota.
  split; [discriminate | exists v; reflexivity].
Qed.

Lemma cnoB_notout : forall lo hi z, ~ outside [(lo, hi)] z -> lo <= z < hi.
Proof.
  intros lo hi z H. split.
  - destruct (Z_le_gt_dec lo z) as [Hl|Hl]; [exact Hl|]. exfalso. apply H. cbn [outside]. split; [lia | exact I].
  - destruct (Z_lt_ge_dec z hi) as [Hl|Hl]; [exact Hl|]. exfalso. apply H. cbn [outside]. split; [lia | exact I].
Qed.

(* The two one-byte flags out_of_memory() reads, in the cell form of the guards (cno_guard1 .. cno_guard3). *)
Lemma cnoB_flags : forall L A m md, J L A m md -> Mem.bytes_at (ms_segs B) m G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
  ro_cells rsegs m GL_OWN_RAN_OUT [C1 (Z_to_bv 8 0)] /\ ro_cells rsegs m G_RAN_OUT [C1 (Z_to_bv 8 0)].
Proof.
  intros L A m md HJ GR. split; apply cno_bytes_ro1; rewrite <- HS.
  - exact (cno_cj_own B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ OWN0).
  - exact GR.
Qed.

(* The run 0x13968 -> 0x15c08 when the three readings succeed (s3 = s4 = s6 = 0): two compare calls on equal
   trees at sp + 0x70, sp + 0x38, sp; s5 = 0. *)
Lemma cnoB_cmp : forall (fx : YK11.FPState) regs m md (L : Z -> Z -> Prop) lo t D1 D2 D0 (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) m ->
  YK11.getr regs 19 = Z_to_bv 64 0 -> YK11.getr regs 20 = Z_to_bv 64 0 -> YK11.getr regs 22 = Z_to_bv 64 0 ->
  bv_unsigned (YK11.getr regs 2) + 168 <= 2 ^ 64 ->
  pj_node (ms_segs B) m L (bv_unsigned (YK11.getr regs 2) + 112) t D1 ->
  pj_node (ms_segs B) m L (bv_unsigned (YK11.getr regs 2) + 56) t D2 ->
  pj_node (ms_segs B) m L (bv_unsigned (YK11.getr regs 2)) t D0 ->
  (forall z, pj_foot (bv_unsigned (YK11.getr regs 2) + 112) D1 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
     outside [(bv_unsigned (YK11.getr regs 2) - same_k t, bv_unsigned (YK11.getr regs 2))] z) ->
  (forall z, pj_foot (bv_unsigned (YK11.getr regs 2) + 56) D2 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
     outside [(bv_unsigned (YK11.getr regs 2) - same_k t, bv_unsigned (YK11.getr regs 2))] z) ->
  (forall z, pj_foot (bv_unsigned (YK11.getr regs 2)) D0 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
     outside [(bv_unsigned (YK11.getr regs 2) - same_k t, bv_unsigned (YK11.getr regs 2))] z) ->
  stk rsegs (normalize rsegs m) lo (bv_unsigned (YK11.getr regs 2)) -> lo + same_k t <= bv_unsigned (YK11.getr regs 2) ->
  (forall regs' mem', YK11.getr regs' 1 = Z_to_bv 64 0x139a8 -> cnoB_keep regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (bv_unsigned (YK11.getr regs 2) + 112) -> YK11.getr regs' 21 = Z_to_bv 64 0 ->
     munch [(bv_unsigned (YK11.getr regs 2) - same_k t, bv_unsigned (YK11.getr regs 2))] m mem' ->
     wmono (ms_segs B) m mem' -> ro_agree (ms_segs B) mem' ->
     pj_node (ms_segs B) mem' L (bv_unsigned (YK11.getr regs 2) + 112) t D1 ->
     pj_node (ms_segs B) mem' L (bv_unsigned (YK11.getr regs 2) + 56) t D2 ->
     pj_node (ms_segs B) mem' L (bv_unsigned (YK11.getr regs 2)) t D0 ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 0x15c08) mem' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x13968) m (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx regs m md L lo t D1 D2 D0 P Hh Hl RA E19 E20 E22 Hsp N1 N2 N0 F1 F2 F0 ST LO K.
  assert (G1 : forall z, pj_foot (bv_unsigned (YK11.getr regs 2) + 112) D1 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z)
    by (intros z Hz; destruct (F1 z Hz) as (H1 & H2 & _); split; assumption).
  assert (G2 : forall z, pj_foot (bv_unsigned (YK11.getr regs 2) + 56) D2 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z)
    by (intros z Hz; destruct (F2 z Hz) as (H1 & H2 & _); split; assumption).
  assert (G0 : forall z, pj_foot (bv_unsigned (YK11.getr regs 2)) D0 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z)
    by (intros z Hz; destruct (F0 z Hz) as (H1 & H2 & _); split; assumption).
  pose proof (cno_node_norm B HS m L _ t D1 N1 G1) as M1.
  pose proof (cno_node_norm B HS m L _ t D2 N2 G2) as M2.
  pose proof (cno_node_norm B HS m L _ t D0 N0 G0) as M0.
  rewrite HS in M1, M2, M0.
  pose proof (mem_inv_normalize rsegs m) as MI.
  apply (cno_run_n B HS regs (Z_to_bv 64 0x13968) m md
    (fun R pc' m' => cmp_some_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (YK11.getr regs 8)
       (YK11.getr regs 9) (YK11.getr regs 18) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25)
       (YK11.getr regs 26) (YK11.getr regs 27) (@fp_regs fx) (@fp_csr fx)
       (normalize rsegs m) L lo t D1 D2 D0 (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk. rewrite E19, E20, E22.
    eapply evt_mono.
    + apply (cno_cmp_some SAME) with (L := L) (lo := lo) (t := t) (D1 := D1) (D2 := D2) (D0 := D0).
      * exact Hsp.
      * exact M1.
      * exact M2.
      * exact M0.
      * exact MI.
      * exact ST.
      * exact LO.
      * intros z Hz. exact (proj2 (proj2 (F1 z Hz))).
      * intros z Hz. exact (proj2 (proj2 (F2 z Hz))).
      * intros z Hz. exact (proj2 (proj2 (F0 z Hz))).
    + intros ms PO. pose proof PO as PO'. unfold cmp_some_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO].
  - intros R pc' m0 mem' regs' HK HREL HRS HGr.
    cbv beta in HK. unfold cmp_some_post in HK.
    destruct HK as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MU & WM & _ & _ &
                    Q1 & Q2 & Q0).
    injection E as ER EP EM. subst R pc' m0.
    rewrite <- HS in MU, WM, Q1, Q2, Q0.
    destruct (cno_back B m mem' m' _ RA HREL HRS MU WM) as (MU' & WM' & RA').
    apply K.
    + rewrite HGr. reflexivity.
    + intros r Hr. rewrite HGr. revert r Hr. cnoB_keepR.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + exact MU'.
    + exact WM'.
    + exact RA'.
    + exact (cno_node_back B HS mem' m' L _ t D1 HREL Q1 G1).
    + exact (cno_node_back B HS mem' m' L _ t D2 HREL Q2 G2).
    + exact (cno_node_back B HS mem' m' L _ t D0 HREL Q0 G0).
Qed.

Lemma cnoB_holds : cno_KC B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x ->
  cno_KB B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x.
Proof.
  intros KC. unfold cno_KB.
  intros fx L A regs m md q1 q2 q3 one two nul HJ Hsp R1 G3 G4 S0 S1 S2 S3 S7 G24 A0r A1r A2r BY FZ LED RF
    Hq1 P1 B1 Hq2 P2 B2 Hq3 P3 B3 N1 N2 N3 HA0 D12 D13 D23 HI.
  pose proof cnoB_num as (HKv & HK & H63 & Hac).
  pose proof cnoB_al as (AL0 & AL56 & AL112).
  pose proof cnoB_nc as NC.
  pose proof ROOM as (_ & _ & _ & RR & _).
  assert (HR : cnoB_R regs one two nul).
  { split; [exact Hsp|]. split; [exact G3|]. split; [exact G4|]. split; [exact S0|]. split; [exact S1|].
    split; [exact S2|]. split; [exact S3|]. split; [exact S7 | exact G24]. }
  pose proof (cno_ub_blocks L A q1 _ Hq1) as QB1. rewrite P1 in QB1.
  pose proof (cno_ub_blocks L A q2 _ Hq2) as QB2. rewrite P2 in QB2.
  pose proof (cno_ub_blocks L A q3 _ Hq3) as QB3. rewrite P3 in QB3.
  pose proof (cno_cj_gro B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ GRO0) as GR0.
  (* reading 1: text one, tree at sp + 0x70 *)
  refine (cno_call_parse B API HS AX HG F PARSE L0 A0 regs0 mem0 md0 PRE0 HTP HERR HGG HGD HSP47 HGLOB
    fx L A regs m md Lam peak cnt (cno_b3 F b nx) one (spZ regs0 - 240 + 112) x _ HJ Hsp G4
    ltac:(rewrite R1; cnoB_ret) FZ LED RF A0r A1r A2r QB1 (cnoB_noLam0 one N1) B1 XLEN
    ltac:(lia) ltac:(lia) AL112 GR0 HI ltac:(lia) RR _).
  intros fx1 L1 A1 regs1 m1 md1 Lam1 pk1 D1 HJ1 RP1 FZ1 LED1 PK1 PM1 NB1 ND1 RV1 GR1 MT1.
  destruct (cnoB_pf A1 (cno_b3 F b nx) D1 MT1) as (E1 & DL1 & RF1 & DT1).
  pose proof (cnoB_R_rp regs regs1 one two nul HR (cnoB_rp RP1)) as HR1.
  pose proof (cnoB_ini RP1 HI) as HI1.
  destruct (cnoB_ub RP1 Hq1 P1) as (Hq1a & P1a & QB1a).
  destruct (cnoB_ub RP1 Hq2 P2) as (Hq2a & P2a & QB2a).
  destruct (cnoB_ub RP1 Hq3 P3) as (Hq3a & P3a & QB3a).
  pose proof (cnoB_bytes q2 two HJ RP1 ltac:(lia) Hq2 P2 B2) as B2a.
  pose proof (cnoB_bytes q3 nul HJ RP1 ltac:(lia) Hq3 P3 B3) as B3a.
  pose proof (cnoB_saved RP1 Hsp ltac:(lia) BY) as BY1.
  pose proof (cnoB_newD HJ NB1 QB1 QB2 QB3) as NDc1.
  pose proof (cnoB_noLam PM1 NB1 QB2 (cnoB_noLam0 two N2)) as NL2.
  pose proof (cnoB_noLam PM1 NB1 QB3 (cnoB_noLam0 nul N3)) as NL3a.
  pose proof HJ1 as (HM1 & _). destruct (kb_md B API L1 A1 m1 md1 HM1) as (Hh1 & Hz1).
  pose proof HR1 as (Hs1 & _ & _ & _ & H91 & _ & H191 & H231 & _).
  destruct (cnoB_flags L1 A1 m1 md1 HJ1 GR1) as (OW1 & GC1).
  (* the out_of_memory() test after reading 1 (0x138b8 .. 0x13924): s4 = r1, s5 = 1, both flags 0 *)
  rewrite R1.
  eapply (cno_jump B HS fx1 regs1 _ m1 md1 _ _ _ Hh1 Hz1).
  { unfold rmk. rewrite H231. apply (cno_guard1 FAR).
    - change (bv_unsigned (YK11.getr regs1 2)) with (spZ regs1). lia.
    - exact OW1.
    - exact GC1. }
  intros regs1' HG1.
  assert (HR1' : cnoB_R regs1' one two nul)
    by (apply (cnoB_R_jump regs1 regs1' _ one two nul HR1 HG1); [cnoB_keepR | reflexivity | reflexivity]).
  pose proof HR1' as (Hs1' & _ & G41' & _).
  assert (A0r1 : YK11.getr regs1' 10 = Z_to_bv 64 two)
    by (transitivity (YK11.getr regs1 9); [rewrite HG1; reflexivity | exact H91]).
  assert (A1r1 : YK11.getr regs1' 11 = Z_to_bv 64 nx)
    by (transitivity (YK11.getr regs1 19); [rewrite HG1; reflexivity | exact H191]).
  assert (A2r1 : YK11.getr regs1' 12 = Z_to_bv 64 (spZ regs0 - 240 + 56)).
  { transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr regs1 2) + 56)); [rewrite HG1; reflexivity|].
    change (bv_unsigned (YK11.getr regs1 2)) with (spZ regs1). rewrite Hs1. reflexivity. }
  assert (RA1 : YK11.getr regs1' 1 = Z_to_bv 64 0x13928) by (rewrite HG1; reflexivity).
  assert (S4a : YK11.getr regs1' 20 = Z_to_bv 64 (cno_rv x))
    by (transitivity (YK11.getr regs1 10); [rewrite HG1; reflexivity | exact RV1]).
  (* reading 2: text two, tree at sp + 0x38 *)
  refine (cno_call_parse B API HS AX HG F PARSE L0 A0 regs0 mem0 md0 PRE0 HTP HERR HGG HGD HSP47 HGLOB
    fx1 L1 A1 regs1' m1 md1 Lam1 pk1 (cnt + nc) (cnoB_nb (cno_b3 F b nx) E1) two (spZ regs0 - 240 + 56) x _
    HJ1 Hs1' G41' ltac:(rewrite RA1; cnoB_ret) FZ1 LED1 RF1 A0r1 A1r1 A2r1 QB2a NL2 B2a XLEN
    ltac:(lia) ltac:(lia) AL56 GR1 HI1 ltac:(lia) (cnoB_room2 E1 DL1) _).
  intros fx2 L2 A2 regs2 m2 md2 Lam2 pk2 D2 HJ2 RP2 FZ2 LED2 PK2 PM2 NB2 ND2 RV2 GR2 MT2.
  destruct (cnoB_pf A2 _ D2 MT2) as (E2 & DL2 & RF2 & DT2).
  pose proof (cnoB_R_rp regs1' regs2 one two nul HR1' (cnoB_rp RP2)) as HR2.
  pose proof (cnoB_ini RP2 HI1) as HI2.
  destruct (cnoB_ub RP2 Hq1a P1a) as (Hq1b & P1b & QB1b).
  destruct (cnoB_ub RP2 Hq2a P2a) as (Hq2b & P2b & QB2b).
  destruct (cnoB_ub RP2 Hq3a P3a) as (Hq3b & P3b & QB3b).
  pose proof (cnoB_bytes q3 nul HJ1 RP2 ltac:(lia) Hq3a P3a B3a) as B3b.
  pose proof (cnoB_saved RP2 Hs1' ltac:(lia) BY1) as BY2.
  pose proof (cnoB_newD HJ1 NB2 QB1a QB2a QB3a) as NDc2.
  pose proof (cnoB_noLam PM2 NB2 QB3a NL3a) as NL3.
  pose proof (cnoB_node HJ1 RP2 LED1 ND1 PM2 Hs1' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ND1b.
  pose proof (cnoB_rp RP2) as RPr2.
  assert (S4b : YK11.getr regs2 20 = Z_to_bv 64 (cno_rv x))
    by (etransitivity; [apply (RPr2 20); unfold callee_saved; lia | exact S4a]).
  pose proof HJ2 as (HM2 & _). destruct (kb_md B API L2 A2 m2 md2 HM2) as (Hh2 & Hz2).
  pose proof HR2 as (Hs2 & _ & _ & _ & _ & H182 & H192 & H232 & _).
  destruct (cnoB_flags L2 A2 m2 md2 HJ2 GR2) as (OW2 & GC2).
  (* the out_of_memory() test after reading 2 (0x13928 .. 0x13950): s6 = r2, both flags 0 *)
  rewrite RA1.
  eapply (cno_jump B HS fx2 regs2 _ m2 md2 _ _ _ Hh2 Hz2).
  { unfold rmk. rewrite H232. apply (cno_guard2 FAR); [exact OW2 | exact GC2]. }
  intros regs2' HG2.
  assert (HR2' : cnoB_R regs2' one two nul)
    by (apply (cnoB_R_jump regs2 regs2' _ one two nul HR2 HG2); [cnoB_keepR | reflexivity | reflexivity]).
  pose proof HR2' as (Hs2' & _ & G42' & _).
  assert (A0r2 : YK11.getr regs2' 10 = Z_to_bv 64 nul)
    by (transitivity (YK11.getr regs2 18); [rewrite HG2; reflexivity | exact H182]).
  assert (A1r2 : YK11.getr regs2' 11 = Z_to_bv 64 nx)
    by (transitivity (YK11.getr regs2 19); [rewrite HG2; reflexivity | exact H192]).
  assert (A2r2 : YK11.getr regs2' 12 = Z_to_bv 64 (spZ regs0 - 240)).
  { transitivity (YK11.getr regs2 2); [rewrite HG2; reflexivity|].
    rewrite <- Hs2. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (RA2 : YK11.getr regs2' 1 = Z_to_bv 64 0x13954) by (rewrite HG2; reflexivity).
  assert (S4c : YK11.getr regs2' 20 = Z_to_bv 64 (cno_rv x))
    by (transitivity (YK11.getr regs2 20); [rewrite HG2; reflexivity | exact S4b]).
  assert (S6c : YK11.getr regs2' 22 = Z_to_bv 64 (cno_rv x))
    by (transitivity (YK11.getr regs2 10); [rewrite HG2; reflexivity | exact RV2]).
  (* reading 3: text nul, tree at sp *)
  refine (cno_call_parse B API HS AX HG F PARSE L0 A0 regs0 mem0 md0 PRE0 HTP HERR HGG HGD HSP47 HGLOB
    fx2 L2 A2 regs2' m2 md2 Lam2 pk2 (cnt + nc + nc) (cnoB_nb (cnoB_nb (cno_b3 F b nx) E1) E2) nul
    (spZ regs0 - 240) x _
    HJ2 Hs2' G42' ltac:(rewrite RA2; cnoB_ret) FZ2 LED2 RF2 A0r2 A1r2 A2r2 QB3b NL3 B3b XLEN
    ltac:(lia) ltac:(lia) AL0 GR2 HI2 ltac:(lia) (cnoB_room3 E1 E2 DL1 DL2) _).
  intros fx3 L3 A3 regs3 m3 md3 Lam3 pk3 D0 HJ3 RP3 FZ3 LED3 PK3 PM3 NB3 ND0 RV3 GR3 MT3.
  destruct (cnoB_pf A3 _ D0 MT3) as (E3 & DL3 & RF3 & DT3).
  pose proof (cnoB_R_rp regs2' regs3 one two nul HR2' (cnoB_rp RP3)) as HR3.
  pose proof (cnoB_ini RP3 HI2) as HI3.
  destruct (cnoB_ub RP3 Hq1b P1b) as (Hq1c & P1c & _).
  destruct (cnoB_ub RP3 Hq2b P2b) as (Hq2c & P2c & _).
  destruct (cnoB_ub RP3 Hq3b P3b) as (Hq3c & P3c & _).
  pose proof (cnoB_saved RP3 Hs2' ltac:(lia) BY2) as BY3.
  pose proof (cnoB_newD HJ2 NB3 QB1b QB2b QB3b) as NDc3.
  pose proof (cnoB_node HJ2 RP3 LED2 ND1b PM3 Hs2' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ND1c.
  pose proof (cnoB_node HJ2 RP3 LED2 ND2 PM3 Hs2' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ND2c.
  pose proof (cnoB_rp RP3) as RPr3.
  assert (S20 : YK11.getr regs3 20 = Z_to_bv 64 (cno_rv x))
    by (etransitivity; [apply (RPr3 20); unfold callee_saved; lia | exact S4c]).
  assert (S22 : YK11.getr regs3 22 = Z_to_bv 64 (cno_rv x))
    by (etransitivity; [apply (RPr3 22); unfold callee_saved; lia | exact S6c]).
  assert (ECT : cnt + nc + nc + nc = ct3) by lia. rewrite ECT in LED3.
  assert (PKs : peak <= pk3) by lia.
  assert (PMs : Permutation Lam3 (D0 ++ D2 ++ D1 ++ Lam)).
  { eapply Permutation_trans; [exact PM3|]. apply Permutation_app_head.
    eapply Permutation_trans; [exact PM2|]. apply Permutation_app_head. exact PM1. }
  assert (DDs : forall a k, In (a, k) (D1 ++ D2 ++ D0) ->
     ~ In (a - 16, k + 16) (blocks L0 A0) /\ (a - 16, k + 16) <> (one, nx + 16) /\
     (a - 16, k + 16) <> (two, nx + 16) /\ (a - 16, k + 16) <> (nul, nx + 16)).
  { intros a k Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (NDc1 a k Hin)|].
    apply in_app_or in Hin as [Hin|Hin]; [exact (NDc2 a k Hin) | exact (NDc3 a k Hin)]. }
  pose proof HJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RA3).
  destruct (kb_md B API L3 A3 m3 md3 HM3) as (Hh3 & Hz3).
  pose proof HR3 as (Hs3 & _ & _ & _ & _ & _ & _ & H233 & _).
  destruct (cnoB_flags L3 A3 m3 md3 HJ3 GR3) as (OW3 & GC3).
  (* the out_of_memory() test after reading 3 (0x13954 .. 0x13964): s3 = r0, ran_out = 0, on to 0x13968 *)
  rewrite RA2.
  eapply (cno_jump B HS fx3 regs3 _ m3 md3 _ _ _ Hh3 Hz3).
  { unfold rmk. rewrite H233. apply (cno_guard3 FAR); [exact OW3 | exact GC3]. }
  intros regs4 HG4.
  assert (KP4 : cnoB_keep regs3 regs4) by (intros r Hr; rewrite HG4; revert r Hr; cnoB_keepR).
  pose proof (cnoB_fin regs3 regs4 one two nul HR3 KP4) as (Hs4 & _).
  assert (S19' : YK11.getr regs4 19 = Z_to_bv 64 (cno_rv x))
    by (transitivity (YK11.getr regs3 10); [rewrite HG4; reflexivity | exact RV3]).
  assert (S20' : YK11.getr regs4 20 = Z_to_bv 64 (cno_rv x))
    by (transitivity (YK11.getr regs3 20); [rewrite HG4; reflexivity | exact S20]).
  assert (S22' : YK11.getr regs4 22 = Z_to_bv 64 (cno_rv x))
    by (transitivity (YK11.getr regs3 22); [rewrite HG4; reflexivity | exact S22]).
  (* the state at the first tree-free call, from either path *)
  assert (FIN : forall regs5 m5, J L3 A3 m5 md3 -> cnoB_keep regs4 regs5 -> YK11.getr regs5 1 = Z_to_bv 64 0x139a8 ->
     YK11.getr regs5 10 = Z_to_bv 64 (spZ regs0 - 240 + 112) -> YK11.getr regs5 21 = Z_to_bv 64 0 ->
     bytes_at rsegs m5 (spZ regs0 - 72) (cno_saved regs0) ->
     Mem.bytes_at (ms_segs B) m5 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
     ledger B L3 A3 m5 Lam3 pk3 ct3 (2 ^ 64 - 1) ->
     pj_node (ms_segs B) m5 (lin Lam3) (spZ regs0 - 240 + 112) ux D1 ->
     pj_node (ms_segs B) m5 (lin Lam3) (spZ regs0 - 240 + 56) ux D2 ->
     pj_node (ms_segs B) m5 (lin Lam3) (spZ regs0 - 240) ux D0 ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx3 regs5 (Z_to_bv 64 0x15c08) m5 (YK11.seg_rom (ms_segs B))) md3)
       (cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x)).
  { intros regs5 m5 HJ5 KP R51 R510 R521 BY5 GR5 LED5 N1' N2' N0'.
    destruct (cnoB_fin regs3 regs5 one two nul HR3 (cnoB_keep_trans regs3 regs4 regs5 KP4 KP))
      as (H2 & H3 & H4 & H8 & H9 & H18 & H24).
    exact (KC fx3 L3 A3 regs5 m5 md3 Lam3 pk3 q1 q2 q3 one two nul ux D1 D2 D0
      (cnoB_nb (cnoB_nb (cnoB_nb (cno_b3 F b nx) E1) E2) E3) HJ5 H2 R51 H3 H4 H8 H9 H18 R521 H24 R510 BY5 GR5 FZ3 LED5
      PKs PMs N1' N2' N0' cnoB_depth DDs Hq1c P1c Hq2c P2c Hq3c P3c HA0 D12 D13 D23 HI3 RF3
      (cnoB_bridge E1 E2 E3 D1 D2 D0 DL1 DL2 DL3 DT1 DT2 DT3)). }
  destruct cnoB_case as [E0|E0].
  - (* the three readings succeeded: the two compare calls *)
    assert (ESP : bv_unsigned (YK11.getr regs4 2) = spZ regs0 - 240) by exact Hs4.
    pose proof cnoB_samek as SK.
    apply (cnoB_cmp fx3 regs4 m3 md3 (lin Lam3) (spZ regs0 - 240 - same_k ux) ux D1 D2 D0 _ Hh3 Hz3 RA3).
    + rewrite S19', E0. reflexivity.
    + rewrite S20', E0. reflexivity.
    + rewrite S22', E0. reflexivity.
    + rewrite ESP. lia.
    + rewrite ESP. exact ND1c.
    + rewrite ESP. exact ND2c.
    + rewrite ESP. exact ND0.
    + rewrite ESP. exact (cnoB_foot HJ3 LED3 ND1c ltac:(lia) ltac:(lia)).
    + rewrite ESP. exact (cnoB_foot HJ3 LED3 ND2c ltac:(lia) ltac:(lia)).
    + rewrite ESP. exact (cnoB_foot HJ3 LED3 ND0 ltac:(lia) ltac:(lia)).
    + rewrite ESP. apply (cnoB_stk L3 A3 m3 md3 _ HJ3); lia.
    + rewrite ESP. lia.
    + intros regs5 m5 R51 KP R510 R521 MU5 WM5 RA5 N1' N2' N0'.
      rewrite ESP in R510, MU5, N1', N2', N0'.
      apply (FIN regs5 m5); [| exact KP | exact R51 | exact R510 | exact R521 | | | | exact N1' | exact N2' | exact N0'].
      * apply (cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0 L3 A3 m3 md3 m5 _ HJ3 MU5 WM5 RA5).
        intros z Hz Ho. left. apply cnoB_notout in Ho. lia.
      * apply (cno_bytes_munch1 m3 m5 _ _ _ _ BY3 MU5). right. lia.
      * rewrite HS in GR3 |- *. apply (cno_bytes_munch1 m3 m5 _ _ _ _ GR3 MU5). left.
        rewrite Mem.length_le1. unfold G_RAN_OUT. lia.
      * apply (cno_ledger_munch B API L3 A3 m3 md3 m5 _ Lam3 pk3 _ _ HM3 LED3 MU5).
        intros z Hz Ho. apply cnoB_notout in Ho. lia.
  - (* the three readings failed: straight to the tree frees *)
    eapply (cno_jump B HS fx3 regs4 _ m3 md3 _ _ _ Hh3 Hz3).
    { unfold rmk. apply cno_cmp_none.
      - rewrite S20', S19'. reflexivity.
      - rewrite S22', S19'. reflexivity.
      - rewrite S19', E0. intros H. vm_compute in H. discriminate H.
      - change (bv_unsigned (YK11.getr regs4 2)) with (spZ regs4). lia. }
    intros regs5 HG5.
    apply (FIN regs5 m3 HJ3).
    + intros r Hr. rewrite HG5. revert r Hr. cnoB_keepR.
    + rewrite HG5. reflexivity.
    + transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr regs4 2) + 112)); [rewrite HG5; reflexivity|].
      change (bv_unsigned (YK11.getr regs4 2)) with (spZ regs4). rewrite Hs4. reflexivity.
    + rewrite HG5. reflexivity.
    + exact BY3.
    + exact GR3.
    + exact LED3.
    + exact ND1c.
    + exact ND2c.
    + exact ND0.
Qed.

End Ph.
