(* Segment G06 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13b60, 0x13c54], U13b68 (v1.9 pc
   0x13b60: rf = 1; ingest's result is 0 or 1, #66 not taken), U13b6c (v1.9 pc 0x13b64) -> U13c64 (v1.9 pc 0x13c58):
   opens_record with its UBSan checks T29-T42 not taken by Φ's heap range (Φ = s7, sum_ok = s11, big = s4, the 1 in
   s2), and when it holds v1.9's store into the 40-byte local `first` at sp+36 (first_frag F2): have = 1
   (`sw s2,36(sp)`), n = blk[8] = Φ[26] (`lbu a2,8(s8)`, `sb a2,40(sp)`) and memcpy(sp+41, blk + 9, n) with
   blk = s8 = Φ + 18, the UBSan checks of blk + 8 and blk + 9 not taken; memcpy at 0x1e2fc. v1.8 stored Φ[36], Φ[37],
   1 and n to the slots sp+40, sp+48, sp+24, sp+32 instead. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u6.
Import ListNotations.
Open Scope Z_scope.

(* An exit of the opens_record chain to 0x13c58: nothing stored. *)
Ltac g06_exit :=
  apply evt_done; do 17 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|];
  split; [intros X; discriminate X | intros _; reflexivity].

(* A byte compare of the chain (bne / bnez against k): equal falls through, different exits. *)
Ltac g06_ne b k :=
  let E := fresh "E" in
  destruct (bv_unsigned b =? k) eqn:E;
  rewrite (u6_eqz b k) by lia; rewrite E; cbn [negb andb]; [ | g06_exit].

(* `sb` of a byte `lbu` loaded: le1 (zxb b) = [b], then the store (when the step has not done it). *)
Ltac g06_sb := try (rewrite le1_zxb; mem_after_store).

(* 0x13b64 -> 0x13c58. *)
Lemma g06_main : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (so bg : bool)
         (b16 b17 b18 b19 b22 b23 b24 b25 b26 : byte) (body j36 j40 jb : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 1 ->
    s11 = Z_to_bv 64 (b2z so) -> s4 = Z_to_bv 64 (b2z bg) -> s8 = Z_to_bv 64 (if bg then phi + 18 else 0) ->
    (so = true -> bg = true) ->
    4096 <= phi -> phi + 50 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m ->
    (so = true ->
       ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] /\ ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] /\
       ov_read_bytes rsegs m (wa (phi + 18)) 1 = Some [b18] /\ ov_read_bytes rsegs m (wa (phi + 19)) 1 = Some [b19] /\
       ov_read_bytes rsegs m (wa (phi + 22)) 1 = Some [b22] /\ ov_read_bytes rsegs m (wa (phi + 23)) 1 = Some [b23] /\
       ov_read_bytes rsegs m (wa (phi + 24)) 1 = Some [b24] /\ ov_read_bytes rsegs m (wa (phi + 25)) 1 = Some [b25] /\
       ov_read_bytes rsegs m (wa (phi + 26)) 1 = Some [b26] /\ bytes_at rsegs m (phi + 26) [b26]) ->
    (so = true -> bv_unsigned b26 <= 22 ->
       bytes_at rsegs m (phi + 27) body /\ length body = Z.to_nat (bv_unsigned b26)) ->
    rw_cells rsegs m (spv + 36) [Cells.CB 4 j36] -> rw_cells rsegs m (spv + 40) [Cells.CB 1 j40] ->
    rw_cells rsegs m (spv + 41) [Cells.CB (Z.to_nat (bv_unsigned b26)) jb] ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13c58) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
         (u6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = true ->
            u32 m' (spv + 36) 1 /\ b8 m' (spv + 40) (bv_unsigned b26) /\ bytes_at rsegs m' (spv + 41) body) /\
         (u6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = false -> m' = m))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b64) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi so bg b16 b17 b18 b19 b22 b23 b24 b25 b26 body j36 j40 jb
    -> -> -> Hs11 Hs4 Hs8 Hsb H1 H2 H3 MI HR HBD C36 C40 C41.
  pose proof (munch_refl [(spv + 36, spv + 76)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (RcLib.byte_range b26) as R26b.
  unfold u6_opn.
  destruct so.
  2:{ (* not sum_ok: 0x13b64 to 0x13c58 *)
      destruct bg; cbn [b2z] in Hs11, Hs4; subst s11 s4; cbn [andb].
      all: step; step; if_true; g06_exit. }
  pose proof (Hsb eq_refl) as Hbg. subst bg.
  cbn [b2z] in Hs11, Hs4. cbv beta iota in Hs8. subst s11 s4 s8. cbn [andb].
  destruct (HR eq_refl) as (R16 & R17 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & B26). clear HR.
  step. step. if_false.
  step. u6_nt false.
  step. step. u6_nt false.
  step. step. u6_nt false.
  step. step. step. g06_ne b16 205.
  step. step. u6_nt false.
  step. step. step. g06_ne b17 234.
  step. step. step. step. g06_ne b18 4.
  step. step. u6_nt false.
  step. step. g06_ne b19 1.
  step. step. u6_nt false.
  step. step. g06_ne b22 0.
  step. step. u6_nt false.
  step. step. step. g06_ne b23 2.
  step. step. u6_nt false.
  step. step. g06_ne b24 0.
  step. step. u6_nt false.
  step. step. step. g06_ne b25 254.
  step. step. u6_nt false.
  step. step.
  (* Φ[26] = 0 exits (0x13c14) *)
  destruct (bv_unsigned b26 =? 0) eqn:E26;
    rewrite (u6_eqz b26 0) by lia; rewrite E26; cbn [negb andb]; [g06_exit|].
  step. step. u6_nt false.
  step. step.
  (* Φ[26] > 22 exits (0x13c24) *)
  destruct (22 <? bv_unsigned b26) eqn:E22;
    rewrite (u6_ltz b26 22) by lia; rewrite E22; cbn [negb andb]; [g06_exit|].
  (* opens_record holds, 1 <= n = Φ[26] <= 22: the store into `first` 0x13c28-0x13c54 *)
  apply Z.eqb_neq in E26. apply Z.ltb_ge in E22.
  destruct (HBD eq_refl E22) as (HB27 & HL27). clear HBD.
  assert (HLb : Z.of_nat (length body) <= 22) by lia.
  (* 0x13c28 addi a0,s8,8; 0x13c2c sw s2,36(sp) (have = 1) *)
  step. step.
  (* 0x13c30 li a1,9; 0x13c34 bltu a0,a1 (blk + 8 wraps) *)
  step. step. u6_nt false.
  (* 0x13c38 lbu a2,8(s8) = Φ[26]; 0x13c3c sb a2,40(sp) (n) *)
  pose proof (u6_ovr _ _ _ B26) as R26'. cbn [length] in R26'.
  step. step. g06_sb.
  (* 0x13c40 beqz s8; 0x13c44 li a0,-10; 0x13c48 bltu a0,s8 (blk + 9 wraps) *)
  step. u6_nt false.
  step. step. u6_nt false.
  (* 0x13c4c addi a1,s8,9; 0x13c50 addi a0,sp,41; 0x13c54 jal memcpy(sp+41, blk + 9, n) *)
  step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := body) (junk := jb); rewrite ?u6_uzxb; rewrite ?MState.unsigned_lit by lia.
    - first [exact HB27 | replace (phi + 18 + 9) with (phi + 27) by lia; exact HB27].
    - exact HL27.
    - exact C41.
    - lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
              Ems & MUc & WMc & _ & HZ & _).
  subst ms'. rewrite ?u6_uzxb in MUc, HZ. rewrite ?MState.unsigned_lit in MUc, HZ by lia.
  rewrite (MState.ret_pc_even 0x13c58) by (first [reflexivity | lia]).
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m3 MU). eapply munch_weaken; [|exact MUc].
    intros x (O1 & _). cbn [Frame.outside]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ m3 WM WMc)|].
  split; [intros _ | intros X; discriminate X].
  split; [|split].
  - unfold u32. apply (bytes_at_transport rsegs _ _ m3 _ _ (u6_c4 _ _ _ C36) MUc).
    cbn [disjoint_from]. rewrite length_le4. split; [lia | exact I].
  - unfold b8. rewrite u6_byte_self. apply (bytes_at_transport rsegs _ _ m3 _ _ (u6_c1 _ _ _ C40) MUc).
    cbn [disjoint_from length]. split; [lia | exact I].
  - exact (sl_rw_bytes _ _ _ _ HZ).
Qed.

Lemma g06_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc spv phi : Z) (so bg : bool)
         (b16 b17 b18 b19 b22 b23 b24 b25 b26 : byte) (body j36 j40 jb : list byte),
    (pc = 0x13b64 \/ (pc = 0x13b60 /\ (a0 = Z_to_bv 64 0 \/ a0 = Z_to_bv 64 1))) ->
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 1 ->
    s11 = Z_to_bv 64 (b2z so) -> s4 = Z_to_bv 64 (b2z bg) -> s8 = Z_to_bv 64 (if bg then phi + 18 else 0) ->
    (so = true -> bg = true) ->
    4096 <= phi -> phi + 50 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m ->
    (so = true ->
       ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] /\ ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] /\
       ov_read_bytes rsegs m (wa (phi + 18)) 1 = Some [b18] /\ ov_read_bytes rsegs m (wa (phi + 19)) 1 = Some [b19] /\
       ov_read_bytes rsegs m (wa (phi + 22)) 1 = Some [b22] /\ ov_read_bytes rsegs m (wa (phi + 23)) 1 = Some [b23] /\
       ov_read_bytes rsegs m (wa (phi + 24)) 1 = Some [b24] /\ ov_read_bytes rsegs m (wa (phi + 25)) 1 = Some [b25] /\
       ov_read_bytes rsegs m (wa (phi + 26)) 1 = Some [b26] /\ bytes_at rsegs m (phi + 26) [b26]) ->
    (so = true -> bv_unsigned b26 <= 22 ->
       bytes_at rsegs m (phi + 27) body /\ length body = Z.to_nat (bv_unsigned b26)) ->
    rw_cells rsegs m (spv + 36) [Cells.CB 4 j36] -> rw_cells rsegs m (spv + 40) [Cells.CB 1 j40] ->
    rw_cells rsegs m (spv + 41) [Cells.CB (Z.to_nat (bv_unsigned b26)) jb] ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13c58) fc None m' (seg_rom rsegs) /\
         munch [(spv + 36, spv + 76)] m m' /\ wmono rsegs m m' /\
         (u6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = true ->
            u32 m' (spv + 36) 1 /\ b8 m' (spv + 40) (bv_unsigned b26) /\ bytes_at rsegs m' (spv + 41) body) /\
         (u6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = false -> m' = m))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pc spv phi so bg b16 b17 b18 b19 b22 b23 b24 b25 b26 body j36 j40 jb
    Hpc Hsp Hs7 Hs2 Hs11 Hs4 Hs8 Hsb H1 H2 H3 MI HR HBD C36 C40 C41.
  destruct Hpc as [-> | [-> [-> | ->]]]; [| step; if_false | step; if_false].
  all: eapply g06_main; eassumption.
Qed.

Section G06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MCPY : memcpy_contract.

Lemma seg_G06 : forall j,
  Hat B APIf ra (Inv_U13c58_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13b60_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U13b64_at B APIf ra empty) j.
Proof.
  intros j H64.
  assert (RUN : forall g phi L A regs mem md pc,
    (pc = 0x13b64 \/
     (pc = 0x13b60 /\ (YK11.getr regs 10 = Z_to_bv 64 0 \/ YK11.getr regs 10 = Z_to_bv 64 1))) ->
    FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
    Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
    GE g j phi regs mem ->
    SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g)).
  { intros g phi L A regs mem md pc Hpc HFR HP HGE.
    destruct (u6_S_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    destruct (u6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
    pose proof alloc_ceiling_lt as Hac.
    pose proof HGE as (HB & HI & HG & HS).
    pose proof HB as (HT & H7 & H1 & H0 & H2 & HC).
    pose proof HT as (HLK & HFC & H23 & HPhi & H18).
    pose proof HC as (H24 & H16 & H1752).
    pose proof HS as (_ & _ & _ & _ & HFI).
    pose proof (u6_len_range (g_in g) j) as (Hl0 & _ & _).
    pose proof (u6_g_len (g_in g) j) as LG.
    pose proof (RcLib.byte_range (nth 26 (t_g (g_in g) j) (Z_to_bv 8 0))) as R26.
    unfold SLOT_K, SLOT_STACK in *.
    assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
    assert (Hso : t_sum_ok (g_in g) j = true -> 50 <= t_len (g_in g) j).
    { intros Hso. unfold t_sum_ok, t_big in Hso. apply andb_prop in Hso as (Hb & _). apply Z.leb_le in Hb. exact Hb. }
    destruct (sl_rw_of_stk _ _ _ (fsp g + 36) 4 ST ltac:(lia) ltac:(lia)) as (j36 & C36).
    destruct (sl_rw_of_stk _ _ _ (fsp g + 40) 1 ST ltac:(lia) ltac:(lia)) as (j40 & C40).
    destruct (sl_rw_of_stk _ _ _ (fsp g + 41) (Z.to_nat (bv_unsigned (nth 26 (t_g (g_in g) j) (Z_to_bv 8 0)))) ST
                ltac:(lia) ltac:(lia)) as (jb & C41).
    eapply (u6_mid B APIf ra empty FF g _ L A regs mem md _ [(fsp g + 36, fsp g + 76)]);
      [exact HFR | exact HP | | | |].
    - intros x Hx O. apply (sl_fp1 g (fsp g + 36) (fsp g + 76) x); [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
    - rewrite sl_mkR_of.
      apply (g06_evt MCPY) with (spv := fsp g) (phi := phi) (so := t_sum_ok (g_in g) j) (bg := t_big (g_in g) j)
        (b16 := nth 16 (t_g (g_in g) j) (Z_to_bv 8 0)) (b17 := nth 17 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b18 := nth 18 (t_g (g_in g) j) (Z_to_bv 8 0)) (b19 := nth 19 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b22 := nth 22 (t_g (g_in g) j) (Z_to_bv 8 0)) (b23 := nth 23 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b24 := nth 24 (t_g (g_in g) j) (Z_to_bv 8 0)) (b25 := nth 25 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b26 := nth 26 (t_g (g_in g) j) (Z_to_bv 8 0))
        (body := RcFrag.fg_body (t_g (g_in g) j))
        (j36 := j36) (j40 := j40) (jb := jb).
      + exact Hpc.
      + exact Hsp.
      + exact H23.
      + exact H18.
      + exact H0.
      + exact H2.
      + exact H24.
      + intros Hs. unfold t_sum_ok in Hs. apply andb_prop in Hs. exact (proj1 Hs).
      + lia.
      + lia.
      + lia.
      + exact (mem_inv_normalize rsegs mem).
      + intros Hs.
        pose proof (u6_norm mem _ _ HMI (u6_ba_g mem phi (g_in g) j HPhi (Hso Hs))) as HG50.
        split; [exact (RcLib.rd_byte rsegs _ phi _ 16 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 17 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 18 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 19 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 22 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 23 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 24 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 25 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 26 HG50 ltac:(lia))|].
        exact (u6_ba_byte _ phi _ 26 HG50 ltac:(lia)).
      + intros Hs H22.
        pose proof (u6_norm mem _ _ HMI (u6_ba_g mem phi (g_in g) j HPhi (Hso Hs))) as HG50.
        assert (Hn22 : fg_n (t_g (g_in g) j) <= 22)
          by (unfold fg_n, bat; change (Z.to_nat 26) with 26%nat; exact H22).
        split.
        * exact (u6_ba_fgbody _ phi _ HG50 LG Hn22).
        * rewrite (u6_fgbody_len _ LG Hn22). unfold fg_n, bat.
          change (Z.to_nat 26) with 26%nat. reflexivity.
      + exact C36.
      + exact C40.
      + exact C41.
    - intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                 -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity | split; reflexivity].
    - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
      destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                      m'' & HE & _ & _ & Hop & Hno).
      injection HE; intros; subst.
      assert (K : u6_kT regs regs') by (unfold u6_kT; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
      assert (E19 : YK11.getr regs' 19 = YK11.getr regs 19) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      assert (E27 : YK11.getr regs' 27 = YK11.getr regs 27) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      assert (AV : u6_av g phi (t_len (g_in g) j) (fsp g + 36) (fsp g + 76)) by (unfold u6_av, u6_out, spk; lia).
      destruct (u6_inv (g_in g) (S j)) as (LI1 & _ & _).
      destruct (u6_lens (g_in g) j) as (_ & LF & _).
      pose proof (u6_FI_S (g_in g) j HFI) as HFI'.
      rewrite (u6_opn_eq (g_in g) j) in Hop, Hno.
      apply H64. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact (u6_FB_keep g j phi regs regs' mem m' _ _ HB K E19 E27 MU AV)|].
      split; [exact (u6_IDb_keep g _ mem m' _ _ HI LI1 MU ltac:(unfold u6_out, spk; lia))|].
      split; [unfold FGj; rewrite u6_tFG_S; exact (u6_FGb_keep g _ mem m' _ _ HG LF MU ltac:(unfold u6_out, spk; lia))|].
      unfold FSj. rewrite (u6_fs_S (g_in g) j) in HFI' |- *. revert HFI' Hop Hno.
      destruct (f_opens (t_len (g_in g) j) (t_g (g_in g) j)) eqn:Eo;
        cbn [fs_have fs_nb fs_body]; intros HFI' Hop Hno.
      + (* opens: have = 1, n = Φ[26], body = fg_body Φ = Φ[27 .. 27 + n) *)
        destruct (Hop eq_refl) as (Q36 & Q40 & Q41).
        pose proof (fun (a : Z) (bs : list byte) => proj2 (bytes_at_rel rsegs _ _ a bs Hrel)) as T.
        assert (Hn22 : fg_n (t_g (g_in g) j) <= 22).
        { unfold f_opens in Eo. apply andb_prop in Eo as (Efr & _).
          destruct (u6_fr_n _ _ Efr) as (_ & Hn). lia. }
        unfold u32, b8 in Q36, Q40.
        unfold FSb, u32, b8. cbn [fs_have fs_nb fs_body].
        refine (conj (T _ _ Q36) (conj (T _ _ Q40) (conj (T _ _ Q41) (conj _ HFI')))).
        rewrite (u6_fgbody_len _ LG Hn22). unfold fg_n, bat.
        change (Z.to_nat 26) with 26%nat. lia.
      + (* no store: `first` as at turn j *)
        rewrite (Hno eq_refl) in Hrel.
        apply (u6_FSb_mem g _ (t_FG (g_in g) j) _ mem m');
          [| exact (u6_fs_nb_range (g_in g) j) | exact HS | exact HFI'].
        intros a bs _ _ X. exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) (u6_norm mem _ _ HMI X)). }
  split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGE & _ & H10).
    assert (Ha : YK11.getr regs 10 = Z_to_bv 64 0 \/ YK11.getr regs 10 = Z_to_bv 64 1).
    { unfold rg in H10. rewrite H10.
      match goal with |- context [fst (RcIdentModel.ING ?x ?y ?z)] =>
        destruct (RcIdentModel.ING_ret x y z) as [E | E]; rewrite E; [left | right]; reflexivity end. }
    exact (RUN g phi L A regs mem md 0x13b60 (or_intror (conj eq_refl Ha)) HFR HP HGE).
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGE).
    exact (RUN g phi L A regs mem md 0x13b64 (or_introl eq_refl) HFR HP HGE).
Qed.

End G06.
