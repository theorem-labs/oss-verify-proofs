From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step Cells Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require YO0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSlotPlan SlotBridge reac_headamp_tx_init_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rg_mkR : forall F pc fc rv m ro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  let ms := MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro in
  rg ms 1 = x1 /\ rg ms 2 = x2 /\ rg ms 3 = x3 /\ rg ms 4 = x4 /\ rg ms 8 = x8 /\ rg ms 9 = x9 /\
  rg ms 10 = x10 /\ rg ms 11 = x11 /\ rg ms 18 = x18 /\ rg ms 19 = x19 /\ rg ms 20 = x20 /\ rg ms 21 = x21 /\
  rg ms 22 = x22 /\ rg ms 23 = x23 /\ rg ms 24 = x24 /\ rg ms 25 = x25 /\ rg ms 26 = x26 /\ rg ms 27 = x27.
Proof. intros. repeat split; reflexivity. Qed.

Lemma memset_z : memset_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (d n : Z) (junk : list byte),
  0 <= d -> 0 <= n -> d + n < 2 ^ 64 -> a1 = Z_to_bv 64 0 ->
  rw_cells rsegs m d [CB (Z.to_nat n) junk] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(d, d + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MS0 ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n junk
    Hd Hn Hdn -> HR HI.
  assert (Ud : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  - apply (MS0 ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk); [rewrite Ud, Un; exact HR | exact HI].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI & RW).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    unfold memset_post in *.
    rewrite Ud, Un in *. change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW.
    exact (conj E (conj MU (conj WM (conj MI RW)))).
Qed.

Theorem seg_epilogue_holds : seg_epilogue.
Proof.
  unfold seg_epilogue. intros x ms H.
  apply evt_canon.
  { intros a b He Ha.
    pose proof (fun k => rg_eqv a b k He) as RG.
    destruct He as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
    unfold sregs, SREGS in *. cbn [map] in *. rewrite !RG.
    rewrite <- ?HF, <- ?Hpc, <- ?Hsvc, <- ?Hrv, <- ?Hfc, <- ?Hm, <- ?Hro. exact Ha. }
  destruct H as [H | H]; destruct H as ((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & Hpay & Hstk & Hinv & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                 Hsp & Hfr & Hal & Hlen & HSlt).
  all: remember (x_sv x) as sv eqn:Esv.
  all: destruct sv as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|v11 [|v12 l]]]]]]]]]]]]];
    cbn in Hlen; try discriminate.
  all: rewrite canon_MS by exact Hsvc; unfold mkR_of.
  all: unfold w64, PC_RET0, PC_FREE_T_RET in Hpc; rewrite Hpc, Hrv, Hro.
  all: assert (E2 : reg_get (ms_regs ms) 2 = Z_to_bv 64 (SPL x)) by exact Hsp.
  all: rewrite E2; unfold SPL, LLVM_FRAME in *.
  all: cbn [rev app map] in Hfr.
  all: remember (x_S x - 608) as SP eqn:ESP.
  all: assert (Hfr' : rw_cells rsegs (ms_mem ms) (SP + 504)
    [C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 (x_ra x)])
    by (replace (SP + 504) with (x_S x - 104) by lia; exact Hfr).
  all: clear Hfr.
  2: zstep.
  all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep;
    zstep; zstep.
  all: apply evt_done; unfold sregs, SREGS, rg, w64; cbn [map].
  all: repeat split; try reflexivity.
  all: cbn [ms_fregs ms_fcsr MS]; try exact HF; try exact Hfc.
  all: try exact Hgp; try exact Htp.
  all: try (change (Z_to_bv 64 (SP + 608) = Z_to_bv 64 (x_S x)); rewrite ESP; f_equal; lia).
Qed.

Theorem seg_init_holds : reac_headamp_tx_init_contract -> memset_contract -> seg_init.
Proof.
  intros INIT MEMSET. unfold seg_init. intros x t ms H.
  apply evt_canon; [apply eqv_and; [apply eqv_kept | apply eqv_At_set0] |].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & Hpay & Hstk & Hinv & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & Hfr & Hal & Hlen & HSlt) & Hn & Ha0 & (Hs27 & Hs25) & Hs1 & Hs3 & Hs2 & Hs4 & Hblk & Ht16 & junk & Htab).
  rewrite canon_MS by exact Hsvc. unfold mkR_of.
  unfold w64, PC_MALLOC_T_RET in Hpc. rewrite Hpc, Hrv, Hro.
  assert (E2 : reg_get (ms_regs ms) 2 = Z_to_bv 64 (SPL x)) by exact Hsp.
  assert (E10 : reg_get (ms_regs ms) 10 = Z_to_bv 64 t) by exact Ha0.
  rewrite E2, E10. unfold blk, x_n in *. unfold SPL, LLVM_STACK in *. unfold LLVM_FRAME, YO0d.ALLOC_STACK in *.
  destruct Hblk as (Ht0 & Htn & Htd & Htpd & Htr).
  unfold CTRL_HEADAMP_ROW in *. unfold CTRL_HEADAMP_BYTES in Hrow. cbn [map] in Hrow.
  remember (x_S x - 608) as SP eqn:ESP.
  remember (ms_mem ms) as m eqn:Em.
  pose proof (munch_refl [(x_S x - 8800, x_S x); (t, t + 460)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Slo : 0 <= x_S x - 8800) by (destruct Hstk as [Hz _]; lia).
  destruct (stk_split rsegs m (x_S x - 8800) (SP + 504) (x_S x) Hstk ltac:(lia)) as [ST STU]. clear Hstk.
  carve_frame 144%nat ST. rename FR into FRw.
  carve_frame 144%nat ST. rename FR into FRs.
  carve_frame 176%nat ST. rename FR into FRx.
  carve_frame 32%nat ST. rename FR into FRo.
  remember (x_sv x) as sv eqn:Esv.
  destruct sv as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|v11 [|v12 l]]]]]]]]]]]]];
    cbn in Hlen; try discriminate.
  cbn [rev app map] in Hfr.
  assert (Hfr' : rw_cells rsegs m (SP + 504)
    [C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 (x_ra x)])
    by (replace (SP + 504) with (x_S x - 104) by lia; exact Hfr).
  clear Hfr.
  zstep.
  if_cases HC1; zify_cond HC1.
  { rewrite ?Z.mod_small in HC1 by lia. lia. }
  zstep. zstep.
  pose proof (fun ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 =>
    INIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 t junk) as INIT'.
  call INIT'.
  1: reflexivity.
  1: lia.
  1: exact Htab.
  1: exact Hinv.
  zstep. zstep. zstep. zstep.
  call (memset_z MEMSET).
  1-3: lia.
  1: reflexivity.
  1: exact FRw.
  1: assumption.
  zstep. zstep. zstep. zstep.
  call (memset_z MEMSET).
  1-3: lia.
  1: reflexivity.
  1: exact FRs.
  1: assumption.
  zstep. zstep. zstep. zstep.
  assert (E9 : reg_get (ms_regs ms) 9 = w64 (h_base (hd x))) by exact Hs1.
  assert (E18 : reg_get (ms_regs ms) 18 = w64 (h_rows (hd x))) by exact Hs2.
  assert (E19 : reg_get (ms_regs ms) 19 = w64 (h_in (hd x))) by exact Hs3.
  assert (E20 : reg_get (ms_regs ms) 20 = w64 (h_hi (hd x))) by exact Hs4.
  rewrite E9, E18, E19, E20 in FRo.
  change (Z.to_nat 144) with 144%nat in POST0, POST1.
  eapply stk_release in ST; [ | exact FRo | lia ]. cbn [cells_size csize Nat.add] in ST.
  replace (SP + 8 + Z.of_nat 32) with (SP + 40) in ST by lia.
  eapply stk_release in ST; [ | exact FRx | lia ]. cbn [cells_size csize Nat.add] in ST.
  replace (SP + 40 + Z.of_nat 176) with (SP + 216) in ST by lia.
  eapply stk_release in ST; [ | exact POST1 | lia ]. cbn [cells_size csize Nat.add] in ST.
  replace (SP + 216 + Z.of_nat 144) with (SP + 360) in ST by lia.
  eapply stk_release in ST; [ | exact POST0 | lia ]. cbn [cells_size csize Nat.add] in ST.
  replace (SP + 360 + Z.of_nat 144) with (SP + 504) in ST by lia.
  pose proof (stk_merge rsegs m1 (x_S x - 8800) (SP + 504) (x_S x) ST STU ltac:(lia)) as STM.
  apply evt_done.
  split.
  { unfold kept. cbn [ms_mem MS]. rewrite <- Em. split; [exact MU | exact WM]. }
  unfold At_set0, body, common, cur, slots, table, arrays.
  cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS].
  repeat match goal with |- _ /\ _ => split end.
  all: cbn [rev app map length].
  all: try (unfold w64, PC_SET0; reflexivity).
  all: try assumption.
  all: try (unfold SPL, LLVM_FRAME; lia).
  all: try (unfold rg, PropExec.getr; cbn -[Z_to_bv]; first [exact Hgp | exact Htp | exact Hs27 | exact Hs25 | reflexivity]).
  all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; exact FRo).
  all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; exact POST0).
  all: try (unfold SPL, LLVM_FRAME; rewrite <- ESP; exact POST1).
  all: try (replace (x_S x - 104) with (SP + 504) by lia; exact Hfr').
  all: try (unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK; exact STM).
  all: try (unfold rg, PropExec.getr, w64, SPL, LLVM_FRAME; cbn -[Z_to_bv]; rewrite ?ESP; reflexivity).
  all: try (rewrite <- Esv; cbn [rev app map]; replace (x_S x - 104) with (SP + 504) by lia; exact Hfr').
  all: try (rewrite <- Esv; reflexivity).
  all: try (unfold blk, x_n, LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK; lia).
  all: try (unfold blk, CTRL_HEADAMP_ROW, CTRL_HEADAMP_BYTES, LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK, x_n;
            cbn [map]; first [exact Hrow | lia]).
Qed.
