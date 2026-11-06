(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the property loop's
   preheader of the build (M01) of LLVMFuzzerTestOneInput 0x7ff88, PH 0x8051c -> N 0x805e8 (nprops <> 0) / P
   0x81ed4 (nprops = 0), pod.h:397-398. Proves no function (kind: segment lemma).

   THE CODE. 0x8051c .. 0x80540 spill a6 (the top word's offset 0), a5 (its address pp), s9 and s6 (F) and
   &pp->n_ent (pp + 0x4d14, from s4 = 0x5000) and its shadow index into R-relative cells; 0x80544 loads nprops
   (R+0x90) and `bnez` 0x80548 leaves to 0x80550 or, through `j` 0x8054c, to P. 0x80550 .. 0x805e4 set the loop's
   registers (seen = 0, i = 0, &t, &r, the `/ 10` multiplier, the shadow address of &pp->len) and the cells the
   property loop reloads (rs_Kc of RPgSeg.v).

   HOW. As RPgW3b.v: the symbolic state is rebuilt from PH's cut over the token engine (no instrumented check runs
   here, so no shadow entry is needed); the R-relative cells are one region with the write window [R, R + 0x100),
   the stack window of the segment's journal, whose seven kept cells are chunks over atoms. Every fact of the end
   cut is read from the final symbolic state: a register from its symbolic value, a cell from its chunk. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg RPgW3b.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================================== PH -> N | P: the preheader =====================================
   0x8051c .. 0x805e4. The R-relative cells are one region with the preheader's write window [R, R + 0x100); the
   seven cells it keeps (fl, nprops, the shape, the shadow address of &pp->len, the cursor, -0x3ffd, the bytes
   left) are its chunks, the five input-dependent ones over the extra atoms 32 .. 36. a6 = 0 and s4 = 0x5000 are
   pinned. The engine stops at `bnez a0` 0x80548 (a0 = nprops); the taken arm runs to N, the other to P. *)
Definition w3b_regs_ph : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 16) (SLit 0)) (Z_to_bv 5 20) (SLit 0x5000).
Definition w3b_slot_ph : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 0x100 0 0x100
[YP09.mkChunk 0x30 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 34 0));
 YP09.mkChunk 0xb0 (CVal 8 w3b_shx); YP09.mkChunk 0xc8 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xe8 (CVal 8 (SLit W3B_M3FFD));
 YP09.mkChunk 0xf8 (CVal 8 (SOff 36 0))].
Definition w3b_atoms_ph : list (nat * afact) := [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0)].
Definition w3b_ss_ph : sstate := mkSS W3B_PH w3b_regs_ph [w3b_slot_ph] None (mkFacts w3b_atoms_ph [] []).

(* the value of a symbolic expression of a final state, from the exact values of its atoms (U facts in context) *)
Ltac w3b_den :=
  unfold w3b_shx; rewrite denot_lit_U; apply Z_to_bv64_eq_mod;
  repeat match goal with H : U ?E ?x = _ |- context [U ?E ?x] => rewrite H end;
  rewrite ?U_SAlu, ?U_SOff, ?U_SLit; cbn [zalu_raw];
  repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite H end;
  rewrite ?Z.add_0_r; unfold zcanon, M64; rewrite ?Zmod_mod;
  first [reflexivity | f_equal; lia | lia].
(* the machine state a final symbolic state describes *)
Ltac w3b_ms HS := lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => m end.
(* one (location, value) fact of a cut, read from the final symbolic state HS: a register from its symbolic value,
   a cell from the region's chunk at that offset *)
Ltac w3b_fact HS E :=
  let ms := w3b_ms HS in
  cbn [fst snd rl_at rl_xv];
  lazymatch goal with
  | |- getr _ ?r = _ =>
      rewrite (st_ok_restrict_reg rsegs _ E _ ms r HS);
      lazymatch goal with |- sv_denot _ (sr_get ?l ?r') = _ =>
        let x := eval vm_compute in (sr_get l r') in change (sr_get l r') with x end;
      unfold w64; w3b_den
  | |- val_mem _ _ (?R + ?o) 8 _ =>
      match goal with C : YP09.chunk_ok _ _ _ R (YP09.mkChunk o (CVal 8 ?ex)) |- _ =>
        apply (val_of_chunk_ok rsegs E _ R o 8 ex _ C);
        [ w3b_den
        | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
        | cbn; lia ]
      end
  end.
Ltac w3b_split_chunks Cs :=
  repeat lazymatch type of Cs with _ /\ _ => let c := fresh "Cn" in destruct Cs as [c Cs] end.
Ltac w3b_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; w3b_kio].
(* the run's writes are the segment's stack window: the R-relative region on atom 9, R = sp0 + (R - sp0) *)
Ltac w3b_awr_slot U9 R sp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp' ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp' fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp));
    [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
(* ... and those bytes are R-relative *)
Ltac w3b_kw U9 :=
  let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (rg & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  destruct Hr as [<-|[]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite U9 in Hb; lia.
(* fold a run's frame into the kept-bytes fact KE (every byte outside [R, R + 0x100) as at PH) *)
Ltac w3b_keep KE U9 R :=
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KW := fresh "KW" in let KE' := fresh "KE" in
    assert (KW : forall a, in_wrange E0 rs a -> R <= a < R + 0x100) by w3b_kw U9;
    pose proof (RPgCfgChanges.kept_run (fun a => R <= a < R + 0x100) _ _ _ _ _ _ KE HFr KW) as KE';
    clear KE KW HFr; rename KE' into KE end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the final region's chunks, one hypothesis each *)
Ltac w3b_chunks HS U9 :=
  let HOK := fresh "HOK" in let Cs := fresh "Cs" in
  pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _); cbn [ss_mem] in HOK;
  pose proof (Forall_inv HOK) as (_ & _ & _ & Cs); cbn [YP09.r_base YP09.r_chunks base_val] in Cs;
  rewrite U9 in Cs; clear HOK; repeat rewrite Forall_cons_iff in Cs; w3b_split_chunks Cs.
(* rs_core at the end: the journal, s1 .. s3 as at the start (their own atoms), the frames, blocks, I/O and meter,
   and every byte outside the segment's write set as at the start (the run wrote only [R, R + 0x100), which is in
   hi_w1's real-frame range [R, R + 0x138)) *)
Ltac w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE :=
  let ms := w3b_ms HS in
  unfold rs_core, rs_mid; split; [exact HJ|];
  split; [let rr := fresh "rr" in let Hrr := fresh "Hrr" in
          intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]];
          (eapply (w3b_reg_kept E _ ms regs2 _ (w_H W2)); [exact HS | exact HAE | vm_compute; reflexivity]) |];
  split; [exact Hfr|]; split; [exact Hperm|];
  split; [eapply same_io_trans; [exact Hio | w3b_kio] |];
  split; [exact Hmo|];
  let a := fresh "a" in let Ha := fresh "Ha" in let HnS := fresh "HnS" in let HnE := fresh "HnE" in
  let X := fresh "X" in
  intros a Ha HnS HnE; rewrite <- (Hkeep a Ha HnS HnE); apply KE; [exact Ha|];
  intros X; cbv beta in X; apply HnE; unfold rs_E1; left; unfold rl_inw; cbn [hi_w1 role_himg_A];
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; cbn [fst snd rl_xv]; lia.
(* the frame's shadow bytes: below the stack, so outside [R, R + 0x100) *)
Ltac w3b_fsh HS HFSH KE W2 mem2 :=
  let ms := w3b_ms HS in
  let i := fresh "i" in let Hi := fresh "Hi" in let X := fresh "X" in
  apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ rs_P0 HFSH);
  intros i Hi; change (length rs_P0) with 52%nat in Hi;
  apply KE; [unfold shadow_addr, SHADOW_OFF; lia | intros X; cbv beta in X; unfold shadow_addr, SHADOW_OFF in X; lia].
(* the block's bytes: below the stack too *)
Ltac w3b_pp HS HPP KE W2 mem2 Lpc :=
  let ms := w3b_ms HS in
  let y := fresh "y" in let Hy := fresh "Hy" in let X := fresh "X" in
  apply (rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ HPP);
  rewrite Lpc; change (Z.of_nat 19744) with 19744;
  intros y Hy; apply KE; [lia | intros X; cbv beta in X; lia].

(* the block's image has its full size at every shape *)
Lemma w3b_len_pc0 : forall sh, 0 <= sh < 8 -> length (pc_image (PbCut sh [] None)) = 19744%nat.
Proof.
intros sh Hsh. assert (H8 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* PH -> N | P *)
Lemma rs_piece_W3b_pre : rs_piece_W3b_pre_stmt rsegs B MT.
Proof.
intros cx POST rest HST HN HP ly2 S2 W2 regs2 mem2 md2 r sh np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
destruct HST as (HPRE & _ & Hlen & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & _ & Hppc & Hfl & _ & _ & _ & _ & _ & _
  & Hfresh).
cbn [hi_rsz hi_cid role_himg_A] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (3, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 3) with 512 in HFc.
assert (Hnp : 0 <= np <= 3) by (assert (0 <= np < 4) by (rewrite Enp; unfold rs_np; apply Z.mod_pos_bound; lia); lia).
assert (Hsh8 : 0 <= sh < 8) by (rewrite Esh; unfold rs_sh; apply Z.mod_pos_bound; lia).
assert (HFd : 0 <= e_F (x_e rsegs cx) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (w3b_len_pc0 sh Hsh8) as Lpc.
(* PH's facts *)
unfold rs_at_cx, rs_at, rs_L_PH, rs_cur2 in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A15 & A16 & A20 & A8 & A9 & A19 & A23 & A21 & A22 & A25 & A27 & C30 & C90 & C98 & Cb0 & Ce8 & Cc8 & Cf8 & _).
cbn [fst snd rl_at rl_xv] in A15, A16, A20, A8, A9, A19, A23, A21, A22, A25, A27, C30, C90, C98, Cb0, Ce8, Cc8, Cf8.
remember (Ereg regs2 [Z_to_bv 64 (e_fl (x_e rsegs cx)); Z_to_bv 64 np; Z_to_bv 64 sh; Z_to_bv 64 (rs_cur rsegs cx rest r);
  Z_to_bv 64 (Z.of_nat (length r))]) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 [Z_to_bv 64 (e_fl (x_e rsegs cx)); Z_to_bv 64 np;
  Z_to_bv 64 sh; Z_to_bv 64 (rs_cur rsegs cx rest r); Z_to_bv 64 (Z.of_nat (length r))]) n) by (intros; subst E; reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; subst E; exact (ew_Ereg_nat regs2 _ n rr Hn)).
assert (Ux : forall n v, (n < 32)%nat -> getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n v Hn Hg Hv. rewrite (EE n (Z_to_bv 5 (Z.of_nat n))), Hg by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 5) with 32; rewrite Z.mod_small; lia). apply unsigned_lit_small. exact Hv. }
assert (U8 : bv_unsigned (ew E 8) = e_S (x_e rsegs cx)) by (apply (Ux 8%nat); [lia | exact A8 | lia]).
assert (U9 : bv_unsigned (ew E 9) = e_R (x_e rsegs cx)) by (apply (Ux 9%nat); [lia | exact A9 | lia]).
assert (U15 : bv_unsigned (ew E 15) = e_pp (x_e rsegs cx)) by (apply (Ux 15%nat); [lia | exact A15 | lia]).
assert (U16 : bv_unsigned (ew E 16) = 0) by (apply (Ux 16%nat); [lia | exact A16 | lia]).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr (e_F (x_e rsegs cx)))
  by (apply (Ux 19%nat); [lia | exact A19 | unfold shadow_addr, SHADOW_OFF; lia]).
assert (U20 : bv_unsigned (ew E 20) = 0x5000) by (apply (Ux 20%nat); [lia | exact A20 | lia]).
assert (U21 : bv_unsigned (ew E 21) = e_pp (x_e rsegs cx) + 0x4000) by (apply (Ux 21%nat); [lia | exact A21 | lia]).
assert (U22 : bv_unsigned (ew E 22) = e_F (x_e rsegs cx)) by (apply (Ux 22%nat); [lia | exact A22 | lia]).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (apply (Ux 23%nat); [lia | exact A23 | unfold SHADOW_OFF; lia]).
assert (U25 : bv_unsigned (ew E 25) = e_F (x_e rsegs cx)) by (apply (Ux 25%nat); [lia | exact A25 | lia]).
assert (U27 : bv_unsigned (ew E 27) = e_pp (x_e rsegs cx)) by (apply (Ux 27%nat); [lia | exact A27 | lia]).
assert (U32 : bv_unsigned (ew E 32) = e_fl (x_e rsegs cx) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 0); apply Z_to_bv_unsigned).
assert (U33 : bv_unsigned (ew E 33) = np mod 2 ^ 64) by (subst E; rewrite (ew_Ereg_extra regs2 _ 1); apply Z_to_bv_unsigned).
assert (U34 : bv_unsigned (ew E 34) = sh mod 2 ^ 64) by (subst E; rewrite (ew_Ereg_extra regs2 _ 2); apply Z_to_bv_unsigned).
assert (U35 : bv_unsigned (ew E 35) = rs_cur rsegs cx rest r mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 3); apply Z_to_bv_unsigned).
assert (U36 : bv_unsigned (ew E 36) = Z.of_nat (length r) mod 2 ^ 64)
  by (subst E; rewrite (ew_Ereg_extra regs2 _ 4); apply Z_to_bv_unsigned).
assert (HUshx : U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 23 0)) = shadow_addr (e_pp (x_e rsegs cx) + 0x4000)).
{ rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U21, U23, !Z.add_0_r.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold shadow_addr, zcanon, M64, SHADOW_OFF.
  assert (0 <= (e_pp (x_e rsegs cx) + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (e_pp (x_e rsegs cx) + 0x4000)) by lia. rewrite (Z.mod_small 2147450880) by lia.
  rewrite (Z.mod_small ((e_pp (x_e rsegs cx) + 0x4000) / 8)) by lia. rewrite Z.mod_small by lia. lia. }
assert (HU68 : U E (SAlu ALU_SRL (SOff 27 19732) (SLit 3)) = Z.shiftr (e_pp (x_e rsegs cx) + 0x4d14) 3).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, U27.
  change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
  rewrite (Z.mod_small (e_pp (x_e rsegs cx) + 19732)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
(* the symbolic state at PH *)
assert (HS : st_ok rsegs E w3b_ss_ph (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 W3B_PH) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3b_ss_ph. apply (entry_st_ok_full rsegs).
  - unfold w3b_regs_ph. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    + rewrite A16. reflexivity.
    + rewrite A20. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. constructor; [|constructor].
    unfold region_ok, w3b_slot_ph. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hstkp; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 ?ex)) =>
      lazymatch goal with C : val_mem _ _ (_ + o) 8 ?v |- _ =>
        apply (chunk_ok_val rsegs E _ _ o 8 ex v);
        [ w3b_den
        | split; [apply Z.mod_pos_bound; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
        | cbn; lia | exact C ] end end.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. cbn. tauto.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3b_atoms_ph atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3b_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x100) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 RS_PH) with (Z_to_bv 64 W3B_PH).
(* 0x8051c .. 0x80544: the spills of the top word's offset and address, F, &pp->n_ent; stop at `bnez a0` *)
aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_N.
{ w3b_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
(* the run wrote only the R-relative window *)
w3b_keep KE U9 (e_R (x_e rsegs cx)).
(* 0x80548 bnez a0, a0 = nprops *)
srr_branch_tok w3b_tbl_ok HS SHOK w3b_Bspan.
- (* nprops <> 0: 0x80550 .. 0x805e4, the loop's registers and cells, to N *)
  rewrite branch_ne_U, U_SOff, U_SLit, U33, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_N.
  { w3b_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3b_keep KE U9 (e_R (x_e rsegs cx)).
  w3b_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HN ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r eq_refl) end.
  unfold rs_cut_N. split; [w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE|].
  split.
  { unfold rs_at_cx, rs_at, rs_L_N, rs_Rc, rs_Rc0, rs_Kc, rs_cur2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3b_fact HS E. }
  split; [w3b_fsh HS HFSH KE W2 mem2|].
  split; [w3b_pp HS HPP KE W2 mem2 Lpc|].
  split; [exact HIN|]. split; [exact HSUF|].
  split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
  split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|]. split; [lia|].
  rewrite Er. reflexivity.
- (* nprops = 0: `j` 0x8054c to P *)
  rewrite branch_ne_U, U_SOff, U_SLit, U33, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok w3b_tbl_ok HS HJ SHOK w3b_Bspan W3B_P.
  { w3b_awr_slot U9 (e_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3b_keep KE U9 (e_R (x_e rsegs cx)).
  w3b_chunks HS U9.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HP ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r) end.
  unfold rs_cut_P, rs_Pbody. split; [split|].
  + w3b_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE.
  + split; [w3b_fsh HS HFSH KE W2 mem2|].
    split; [w3b_pp HS HPP KE W2 mem2 Lpc|].
    split; [exact HIN|]. split; [exact HSUF|].
    split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
    split; [exact Hlen|]. split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|].
    rewrite Er. reflexivity.
  + unfold rs_at_cx, rs_at, rs_L_P, rs_cur2. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3b_fact HS E.
Qed.
End d.
End b.
