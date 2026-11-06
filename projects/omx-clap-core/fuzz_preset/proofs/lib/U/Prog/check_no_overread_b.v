From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c memset_c same_c pj_parse_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_c check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* Phase B of check_no_overread (#102 ubsan, entry 0x13868, frame 240): from the first parse_noting call (0x13a38,
   ra 0x1392c) through the three readings (trees at sp + 0x70, sp + 0x38, sp; results in s5, s6, s4), each followed
   by its out_of_memory() test (cno_segR1, cno_segR2, cno_segR3: g_own_ran_out and g_ran_out both 0, so no test runs
   out), and, when the readings succeeded, the two compare calls, to the first pj_free call (0x16340, ra 0x139d8,
   s3 = ran_out = 0).  The ran-out arms (s5 / s6 / s4 := -1, the jumps to 0x139d0 with s3 = 1) are not reached: every
   lbu of g_own_ran_out reads the entry's 0 and every fuzz_alloc_ran_out returns the entry's 0 of g_ran_out (both
   bytes kept along the frame invariant cj: cno_cj_own, cno_cj_gro, and g_ran_out in parse_noting's post). *)

Ltac cnoB_ret := unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Ltac cnoB_keepR :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

Section Ph.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.
Hypothesis RD0 : rd_cells B mem0.
Hypothesis HTP : ms_tp B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_TP.
Hypothesis HERR : errno_addr B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis HGG : ms_got_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs0 - CNO_K.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (data : Z) (x : list byte).
Hypothesis LED0 : ledger B L0 A0 mem0 Lam peak cnt (2 ^ 64 - 1).
Hypothesis CNT0 : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis XLEN : Z.of_nat (length x) <= 0x300000.
Hypothesis XB : Mem.bytes_at (ms_segs B) mem0 data x.
Hypothesis XBLK : x <> [] -> exists a k, In (a, k) (blocks L0 A0) /\ a <= data /\ data + Z.of_nat (length x) <= a + k.
Hypothesis ROOM : cno_room F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x).
Hypothesis GRO0 : Mem.bytes_at (ms_segs B) mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Hypothesis OWN0 : Mem.bytes_at (ms_segs B) mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).

Let J := cj B API L0 A0 regs0 mem0 md0.

Local Abbreviation nx := (Z.of_nat (length x)).
Local Abbreviation nc := (Z.of_nat (ncalls jr_strtod (zb x))).
Local Abbreviation ct3 := (cnt + 3 * Z.of_nat (ncalls jr_strtod (zb x))).
Local Abbreviation trx := (cno_tr x).
Local Abbreviation ux := (cno_tv (json_read jr_strtod (zb x))).

(* The bound one parse leaves, and the list of the tree it builds, uniform over the parse outcome. *)
Definition cnoB_nb (bnd : rf_R F) (E : list (Z * Z)) : rf_R F :=
  match json_read jr_strtod (zb x) with
  | Some _ => rf_run F bnd (cno_tr x)
  | None => rf_frees F (rf_run F bnd (cno_tr x)) E
  end.

Definition cnoB_dt (D : list (Z * Z)) : Prop :=
  match json_read jr_strtod (zb x) with Some _ => cno_dl (cno_tr x) D | None => D = [] end.

(* The registers phase B keeps: sp, gp, tp, s0 = one, s1 = two, s2 = nul, s7 = CNO_S7, s8..s11. *)
Definition cnoB_R (regs : bvmap 5 word) (one two nul : Z) : Prop :=
  spZ regs = spZ regs0 - 240 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 = Z_to_bv 64 one /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 two /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18 = Z_to_bv 64 nul /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23 = Z_to_bv 64 CNO_S7 /\
  (forall r, 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)).

Definition cnoB_keep (regs regs' : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ 24 <= r <= 27) ->
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r).

Lemma cnoB_num : 10096 <= CNO_K /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling + CNO_K <= spZ regs0 /\ spZ regs0 < 2 ^ 63 /\
  140735332483072 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Proof.
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & H63 & _). pose proof cno_k_le. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  split; [lia|]. split; [exact HK|]. split; [exact H63|]. lia.
Qed.

Lemma cnoB_al : (spZ regs0 - 240 + 112) mod 8 = 0 /\ (spZ regs0 - 240 + 56) mod 8 = 0 /\ (spZ regs0 - 240) mod 8 = 0.
Proof.
  pose proof PRE0 as (_ & _ & _ & _ & H16 & _). clear -H16.
  repeat split; Z.div_mod_to_equations; lia.
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
  intros regs regs' one two nul (Hs & H3 & H4 & H8 & H9 & H18 & H23 & H24) RP.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (RP 2); unfold callee_saved; lia|].
  split; [rewrite <- H3; apply (RP 3); unfold callee_saved; lia|].
  split; [rewrite <- H4; apply (RP 4); unfold callee_saved; lia|].
  split; [rewrite <- H8; apply (RP 8); unfold callee_saved; lia|].
  split; [rewrite <- H9; apply (RP 9); unfold callee_saved; lia|].
  split; [rewrite <- H18; apply (RP 18); unfold callee_saved; lia|].
  split; [rewrite <- H23; apply (RP 23); unfold callee_saved; lia|].
  intros r Hr. rewrite <- (H24 r Hr). apply RP. unfold callee_saved. lia.
Qed.

Lemma cnoB_fin : forall regs regs' one two nul, cnoB_R regs one two nul -> cnoB_keep regs regs' ->
  spZ regs' = spZ regs0 - 240 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 8 = Z_to_bv 64 one /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 9 = Z_to_bv 64 two /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 18 = Z_to_bv 64 nul /\
  (forall r, 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)).
Proof.
  intros regs regs' one two nul (Hs & H3 & H4 & H8 & H9 & H18 & _ & H24) K.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (K 2); lia|].
  split; [rewrite <- H3; apply (K 3); lia|].
  split; [rewrite <- H4; apply (K 4); lia|].
  split; [rewrite <- H8; apply (K 8); lia|].
  split; [rewrite <- H9; apply (K 9); lia|].
  split; [rewrite <- H18; apply (K 18); lia|].
  intros r Hr. rewrite <- (H24 r Hr). apply K. lia.
Qed.

(* A straight-line run that keeps the registers of cnoB_keep and sets s7 = CNO_S7 again keeps cnoB_R. *)
Lemma cnoB_R_jump : forall regs regs' R one two nul, cnoB_R regs one two nul ->
  (forall r, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' r = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R r) -> cnoB_keep regs R ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R 23 = Z_to_bv 64 CNO_S7 ->
  cnoB_R regs' one two nul.
Proof.
  intros regs regs' R one two nul HR HGr K K23.
  assert (K' : cnoB_keep regs regs') by (intros r Hr; rewrite HGr; exact (K r Hr)).
  destruct (cnoB_fin regs regs' one two nul HR K') as (Hs & H3 & H4 & H8 & H9 & H18 & H24).
  split; [exact Hs|]. split; [exact H3|]. split; [exact H4|]. split; [exact H8|]. split; [exact H9|].
  split; [exact H18|]. split; [rewrite HGr; exact K23 | exact H24].
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

(* A copy block survives a parse: the parse writes only its tree and the alloc statics, neither of which is a byte
   of a block. *)
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
  - unfold scratch_k. rewrite HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
  - intros [Hw|Hs]; [lia|].
    destruct (cno_statics_free B API HG _ Hs) as (_ & Hl & _). lia.
Qed.

Lemma cnoB_node {L A regs m md L' A' regs' m' md' out Lam1 Lam2 D' pk ct fl p t D} : J L A m md ->
  rpost B API PN_K L A regs m md (parse_noting_writes out) (fun _ _ => False) L' A' regs' m' md' ->
  ledger B L A m Lam1 pk ct fl -> pj_node (ms_segs B) m (lin Lam1) p t D -> Permutation Lam2 (D' ++ Lam1) ->
  spZ regs = spZ regs0 - 240 -> spZ regs0 - 240 <= out -> spZ regs0 - 240 <= p ->
  p + 56 <= spZ regs0 -> (p + 56 <= out \/ out + 56 <= p) ->
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
    + unfold scratch_k. rewrite HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
    + intros [Hw|Hs]; [lia|].
      destruct (cno_statics_free B API HG _ Hs) as (_ & Hl & _). lia.
  - intros a k Hin. split; [intros []|]. intros i Hi HE.
    destruct (ledger_block_range B API L A m md Lam1 pk ct fl a k HM HL (HinL a k Hin)) as (R1 & R2 & R3).
    pose proof HL as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
    destruct (FA (a, k) (HinL a k Hin)) as (_ & _ & _ & HNI). cbn [fst snd] in HNI.
    destruct HE as [Hw|Hs]; [lia|].
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

(* The ledger entries are aligned heap blocks below 2^47: the ledger premise of the compare contract. *)
Lemma cnoB_sl {L A m md Lam' pk ct fl} : J L A m md -> ledger B L A m Lam' pk ct fl -> same_ledger (lin Lam').
Proof.
  intros HJ HL. pose proof HJ as (HM & _). unfold same_ledger, lin. intros a k Hin.
  destruct (ledger_block_range B API L A m md Lam' pk ct fl a k HM HL Hin) as (R1 & R2 & R3).
  pose proof (ledger_block_aligned B API L A m md Lam' pk ct fl a k HM HL Hin) as Al.
  split; [lia|]. split; [|lia].
  clear - Al. Z.div_mod_to_equations. lia.
Qed.

(* The run 0x13998 -> 0x16340 when the three readings succeeded (s4 = s5 = s6 = 0): two compare calls on equal
   trees, s3 = 0, a0 = sp + 0x70. *)
Lemma cnoB_cmp : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs m md (L : Z -> Z -> Prop) lo t D1 D2 D0 (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) m ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20 = Z_to_bv 64 0 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21 = Z_to_bv 64 0 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22 = Z_to_bv 64 0 ->
  bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 168 <= 2 ^ 64 -> same_ledger L ->
  pj_node (ms_segs B) m L (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 112) t D1 ->
  pj_node (ms_segs B) m L (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 56) t D2 ->
  pj_node (ms_segs B) m L (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) t D0 ->
  (forall z, pj_foot (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 112) D1 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
     outside [(bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) - same_k t, bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2))] z) ->
  (forall z, pj_foot (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 56) D2 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
     outside [(bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) - same_k t, bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2))] z) ->
  (forall z, pj_foot (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) D0 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\
     outside [(bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) - same_k t, bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2))] z) ->
  stk rsegs (normalize rsegs m) lo (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) -> lo + same_k t <= bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) ->
  (forall regs' mem', OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 1 = Z_to_bv 64 0x139d8 -> cnoB_keep regs regs' ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 19 = Z_to_bv 64 0 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 112) ->
     munch [(bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) - same_k t, bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2))] m mem' ->
     wmono (ms_segs B) m mem' -> ro_agree (ms_segs B) mem' ->
     pj_node (ms_segs B) mem' L (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 112) t D1 ->
     pj_node (ms_segs B) mem' L (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 56) t D2 ->
     pj_node (ms_segs B) mem' L (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) t D0 ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs' (Z_to_bv 64 0x16340) mem' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x13998) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx regs m md L lo t D1 D2 D0 P Hh Hl RA E20 E21 E22 Hsp LG N1 N2 N0 F1 F2 F0 ST LO K.
  assert (G1 : forall z, pj_foot (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 112) D1 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z)
    by (intros z Hz; destruct (F1 z Hz) as (H1 & H2 & _); split; assumption).
  assert (G2 : forall z, pj_foot (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) + 56) D2 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z)
    by (intros z Hz; destruct (F2 z Hz) as (H1 & H2 & _); split; assumption).
  assert (G0 : forall z, pj_foot (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) D0 z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z)
    by (intros z Hz; destruct (F0 z Hz) as (H1 & H2 & _); split; assumption).
  pose proof (cno_node_norm B HS m L _ t D1 N1 G1) as M1.
  pose proof (cno_node_norm B HS m L _ t D2 N2 G2) as M2.
  pose proof (cno_node_norm B HS m L _ t D0 N0 G0) as M0.
  rewrite HS in M1, M2, M0.
  pose proof (mem_inv_normalize rsegs m) as MI.
  apply (cno_run_n B HS regs (Z_to_bv 64 0x13998) m md
    (fun R pc' m' => cmp_some_post (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (@fp_regs fx) (@fp_csr fx)
       (normalize rsegs m) L lo t D1 D2 D0 (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk. rewrite E20, E21, E22.
    eapply evt_mono.
    + apply (cno_cmp_some SAME) with (L := L) (lo := lo) (t := t) (D1 := D1) (D2 := D2) (D0 := D0).
      * exact Hsp.
      * exact LG.
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
  intros fx L A regs m md q1 q2 q3 one two nul HJ Hsp R1 G3 G4 S0 S1 S2 S4 S3 S7 G24 A0r A1r A2r BY FZ LED RF
    Hq1 P1 B1 Hq2 P2 B2 Hq3 P3 B3 N1 N2 N3 HA0 D12 D13 D23 HI.
  pose proof cnoB_num as (HKv & HK & H63 & Hac).
  pose proof cnoB_al as (AL112 & AL56 & AL0).
  pose proof cnoB_nc as NC.
  pose proof ROOM as (_ & _ & _ & RR & _).
  assert (HR : cnoB_R regs one two nul).
  { split; [exact Hsp|]. split; [exact G3|]. split; [exact G4|]. split; [exact S0|]. split; [exact S1|].
    split; [exact S2|]. split; [exact S7 | exact G24]. }
  pose proof (cno_ub_blocks L A q1 _ Hq1) as QB1. rewrite P1 in QB1.
  pose proof (cno_ub_blocks L A q2 _ Hq2) as QB2. rewrite P2 in QB2.
  pose proof (cno_ub_blocks L A q3 _ Hq3) as QB3. rewrite P3 in QB3.
  pose proof (cno_cj_gro B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ GRO0) as GR0.
  (* parse 1: text one, tree at sp + 112 *)
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
  pose proof HR1 as (Hs1 & _ & _ & _ & H91 & _ & H231 & _).
  assert (S41 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 20 = Z_to_bv 64 nx)
    by (rewrite <- S4; apply (cnoB_rp RP1 20); unfold callee_saved; lia).
  pose proof (cno_cj_own B API HS HG L0 A0 regs0 mem0 md0 PRE0 L1 A1 m1 md1 HJ1 OWN0) as OW1.
  rewrite HS in OW1.
  assert (GR1' : bytes_at rsegs m1 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0))) by (rewrite <- HS; exact GR1).
  rewrite R1.
  (* 0x1392c: s5 = the first result; out_of_memory() reads 0 twice; a0 = s1, a1 = s4, a2 = sp + 56 *)
  eapply (cno_jump B HS fx1 regs1 _ m1 md1 _ _ _ Hh1 Hz1).
  { unfold rmk. rewrite H231. apply cno_segR1; [| exact OW1 | exact GR1'].
    change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2)) with (spZ regs1). lia. }
  intros regs1' HG1.
  assert (HR1' : cnoB_R regs1' one two nul)
    by (apply (cnoB_R_jump regs1 regs1' _ one two nul HR1 HG1); [cnoB_keepR | reflexivity]).
  pose proof HR1' as (Hs1' & _ & G41' & _).
  assert (A0r1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1' 10 = Z_to_bv 64 two)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 9); [rewrite HG1; reflexivity | exact H91]).
  assert (A1r1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1' 11 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 20); [rewrite HG1; reflexivity | exact S41]).
  assert (A2r1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1' 12 = Z_to_bv 64 (spZ regs0 - 240 + 56)).
  { transitivity (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2) + 56)); [rewrite HG1; reflexivity|].
    change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2)) with (spZ regs1). rewrite Hs1. reflexivity. }
  assert (RA1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1' 1 = Z_to_bv 64 0x13958) by (rewrite HG1; reflexivity).
  assert (S4a : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1' 20 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 20); [rewrite HG1; reflexivity | exact S41]).
  assert (S5a : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1' 21 = Z_to_bv 64 (cno_rv x))
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 10); [rewrite HG1; reflexivity | exact RV1]).
  (* parse 2: text two, tree at sp + 56 *)
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
  assert (S4b : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 20 = Z_to_bv 64 nx)
    by (etransitivity; [apply (RPr2 20); unfold callee_saved; lia | exact S4a]).
  assert (S5b : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 21 = Z_to_bv 64 (cno_rv x))
    by (etransitivity; [apply (RPr2 21); unfold callee_saved; lia | exact S5a]).
  pose proof HJ2 as (HM2 & _). destruct (kb_md B API L2 A2 m2 md2 HM2) as (Hh2 & Hz2).
  pose proof HR2 as (Hs2 & _ & _ & _ & _ & H182 & H232 & _).
  pose proof (cno_cj_own B API HS HG L0 A0 regs0 mem0 md0 PRE0 L2 A2 m2 md2 HJ2 OWN0) as OW2.
  rewrite HS in OW2.
  assert (GR2' : bytes_at rsegs m2 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0))) by (rewrite <- HS; exact GR2).
  rewrite RA1.
  (* 0x13958: s6 = the second result; out_of_memory() reads 0 twice; a0 = s2, a1 = s4, a2 = sp *)
  eapply (cno_jump B HS fx2 regs2 _ m2 md2 _ _ _ Hh2 Hz2).
  { unfold rmk. rewrite H232. apply cno_segR2; [exact OW2 | exact GR2']. }
  intros regs2' HG2.
  assert (HR2' : cnoB_R regs2' one two nul)
    by (apply (cnoB_R_jump regs2 regs2' _ one two nul HR2 HG2); [cnoB_keepR | reflexivity]).
  pose proof HR2' as (Hs2' & _ & G42' & _).
  assert (A0r2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2' 10 = Z_to_bv 64 nul)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 18); [rewrite HG2; reflexivity | exact H182]).
  assert (A1r2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2' 11 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 20); [rewrite HG2; reflexivity | exact S4b]).
  assert (A2r2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2' 12 = Z_to_bv 64 (spZ regs0 - 240)).
  { transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 2); [rewrite HG2; reflexivity|].
    rewrite <- Hs2. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (RA2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2' 1 = Z_to_bv 64 0x13984) by (rewrite HG2; reflexivity).
  assert (S5c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2' 21 = Z_to_bv 64 (cno_rv x))
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 21); [rewrite HG2; reflexivity | exact S5b]).
  assert (S6c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2' 22 = Z_to_bv 64 (cno_rv x))
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 10); [rewrite HG2; reflexivity | exact RV2]).
  (* parse 3: text nul, tree at sp *)
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
  assert (S5d : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 21 = Z_to_bv 64 (cno_rv x))
    by (etransitivity; [apply (RPr3 21); unfold callee_saved; lia | exact S5c]).
  assert (S6d : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 22 = Z_to_bv 64 (cno_rv x))
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
  pose proof HR3 as (Hs3 & _ & _ & _ & _ & _ & H233 & _).
  pose proof (cno_cj_own B API HS HG L0 A0 regs0 mem0 md0 PRE0 L3 A3 m3 md3 HJ3 OWN0) as OW3.
  rewrite HS in OW3.
  assert (GR3' : bytes_at rsegs m3 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0))) by (rewrite <- HS; exact GR3).
  (* the state at the first tree-free call, from either path *)
  assert (FIN : forall regs4 m4, J L3 A3 m4 md3 -> cnoB_keep regs3 regs4 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 1 = Z_to_bv 64 0x139d8 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 19 = Z_to_bv 64 0 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 10 = Z_to_bv 64 (spZ regs0 - 240 + 112) ->
     bytes_at rsegs m4 (spZ regs0 - 72) (cno_saved regs0) ->
     ledger B L3 A3 m4 Lam3 pk3 ct3 (2 ^ 64 - 1) ->
     pj_node (ms_segs B) m4 (lin Lam3) (spZ regs0 - 240 + 112) ux D1 ->
     pj_node (ms_segs B) m4 (lin Lam3) (spZ regs0 - 240 + 56) ux D2 ->
     pj_node (ms_segs B) m4 (lin Lam3) (spZ regs0 - 240) ux D0 ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx3 regs4 (Z_to_bv 64 0x16340) m4 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md3)
       (cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x)).
  { intros regs4 m4 HJ4 KP R41 R419 R410 BY4 LED4 N1' N2' N0'.
    destruct (cnoB_fin regs3 regs4 one two nul HR3 KP) as (H2 & H3 & H4 & H8 & H9 & H18 & H24).
    pose proof (cno_cj_gro B API HS HG L0 A0 regs0 mem0 md0 PRE0 L3 A3 m4 md3 HJ4 GRO0) as GR4.
    exact (KC fx3 L3 A3 regs4 m4 md3 Lam3 pk3 q1 q2 q3 one two nul ux D1 D2 D0
      (cnoB_nb (cnoB_nb (cnoB_nb (cno_b3 F b nx) E1) E2) E3) HJ4 H2 R41 H3 H4 H8 H9 H18 R419 H24 R410 BY4 GR4 FZ3
      LED4 PKs PMs N1' N2' N0' cnoB_depth DDs Hq1c P1c Hq2c P2c Hq3c P3c HA0 D12 D13 D23 HI3 RF3
      (cnoB_bridge E1 E2 E3 D1 D2 D0 DL1 DL2 DL3 DT1 DT2 DT3)). }
  rewrite RA2.
  (* 0x13984: s4 = the third result; ran_out = out_of_memory() = 0, to the compare block at 0x13998 *)
  eapply (cno_jump B HS fx3 regs3 _ m3 md3 _ _ _ Hh3 Hz3).
  { unfold rmk. rewrite H233. apply cno_segR3; [exact OW3 | exact GR3']. }
  intros regs3' HG3.
  assert (KP3 : cnoB_keep regs3 regs3') by (unfold cnoB_keep; intros r Hr; rewrite HG3; revert r Hr; cnoB_keepR).
  destruct (cnoB_fin regs3 regs3' one two nul HR3 KP3) as (Hs3' & G33 & G43 & G83 & G93 & G183 & G243).
  assert (S20' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 20 = Z_to_bv 64 (cno_rv x))
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 10); [rewrite HG3; reflexivity | exact RV3]).
  assert (S21' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 21 = Z_to_bv 64 (cno_rv x))
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 21); [rewrite HG3; reflexivity | exact S5d]).
  assert (S22' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 22 = Z_to_bv 64 (cno_rv x))
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 22); [rewrite HG3; reflexivity | exact S6d]).
  assert (KPc : forall regs4, cnoB_keep regs3' regs4 -> cnoB_keep regs3 regs4)
    by (intros regs4 KP4 r Hr; rewrite (KP4 r Hr); exact (KP3 r Hr)).
  destruct cnoB_case as [E0|E0].
  - (* the three readings succeeded: the two compare calls *)
    assert (ESP : bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 2) = spZ regs0 - 240) by exact Hs3'.
    pose proof cnoB_samek as SK.
    apply (cnoB_cmp fx3 regs3' m3 md3 (lin Lam3) (spZ regs0 - 240 - same_k ux) ux D1 D2 D0 _ Hh3 Hz3 RA3).
    + rewrite S20', E0. reflexivity.
    + rewrite S21', E0. reflexivity.
    + rewrite S22', E0. reflexivity.
    + rewrite ESP. lia.
    + exact (cnoB_sl HJ3 LED3).
    + rewrite ESP. exact ND1c.
    + rewrite ESP. exact ND2c.
    + rewrite ESP. exact ND0.
    + rewrite ESP. exact (cnoB_foot HJ3 LED3 ND1c ltac:(lia) ltac:(lia)).
    + rewrite ESP. exact (cnoB_foot HJ3 LED3 ND2c ltac:(lia) ltac:(lia)).
    + rewrite ESP. exact (cnoB_foot HJ3 LED3 ND0 ltac:(lia) ltac:(lia)).
    + rewrite ESP. apply (cnoB_stk L3 A3 m3 md3 _ HJ3); lia.
    + rewrite ESP. lia.
    + intros regs4 m4 R41 KP4 R419 R410 MU4 WM4 RA4 N1' N2' N0'.
      rewrite ESP in R410, MU4, N1', N2', N0'.
      apply (FIN regs4 m4); [| exact (KPc regs4 KP4) | exact R41 | exact R419 | exact R410 | | | exact N1' | exact N2'
        | exact N0'].
      * apply (cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0 L3 A3 m3 md3 m4 _ HJ3 MU4 WM4 RA4).
        intros z Hz Ho. left. apply cnoB_notout in Ho. lia.
      * apply (cno_bytes_munch1 m3 m4 _ _ _ _ BY3 MU4). right. lia.
      * apply (cno_ledger_munch B API L3 A3 m3 md3 m4 _ Lam3 pk3 _ _ HM3 LED3 MU4).
        intros z Hz Ho. apply cnoB_notout in Ho. lia.
  - (* the three readings failed: straight to the tree frees *)
    eapply (cno_jump B HS fx3 regs3' _ m3 md3 _ _ _ Hh3 Hz3).
    { unfold rmk. apply cno_cmp_none.
      - rewrite S21', S20'. reflexivity.
      - rewrite S22', S20'. reflexivity.
      - rewrite S20', E0. intros H. vm_compute in H. discriminate H.
      - change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 2)) with (spZ regs3'). lia. }
    intros regs4 HG4.
    apply (FIN regs4 m3 HJ3).
    + apply KPc. intros r Hr. rewrite HG4. revert r Hr. cnoB_keepR.
    + rewrite HG4. reflexivity.
    + rewrite HG4. reflexivity.
    + transitivity (Z_to_bv 64 (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 2) + 112)); [rewrite HG4; reflexivity|].
      change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3' 2)) with (spZ regs3'). rewrite Hs3'. reflexivity.
    + exact BY3.
    + exact LED3.
    + exact ND1c.
    + exact ND2c.
    + exact ND0.
Qed.

End Ph.
