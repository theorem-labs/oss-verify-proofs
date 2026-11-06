(* Segment G06 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x139e4, 0x13a7c], K139e4 (rf = 1; ingest's result
   is 0 or 1), K139e8 -> K13a80 (s2 = -7; opens_record, and when it holds the store of `first`, first_frag F2).
   libreac v1.9.0 (table 5a S_G06, CHANGED: code, new-call, new-insert, operand, register; NEW 0x139e4-0x13a7c from
   the v1.9.0 listing): sum_ok is s1 (0x139e8 `and a0,s2,s1`; v1.8 s0); Φ[26] goes to s8 (0x13a4c `lbu s8,26(s5)`)
   and the range check is 0x13a50-0x13a58; an opening FIRST runs fuzz/fuzz_ctrl.c v1.9.0:407-411:
   memcpy(first.body = sp+40, block + 9 = Φ+27, Φ[26]) by its contract (memcpy_c, 0x13a68), have = 1
   (0x13a6c-0x13a70 `sd a0,16(sp)`), nb = Φ[26] (0x13a74 `mv s3,s8`) - v1.8 stored Φ[36] / Φ[37] / 1 / Φ[26] to
   [sp+32] / [sp+24] / [sp+40] / [sp+16]. The write set is [sp+16, sp+24) and the body buffer [sp+40, sp+76)
   (v1.8 [sp+16, sp+48)); s3, s8 and the caller-saved registers are not kept, so the bundles are carried by the
   local g06_kT / g06_FT_keep / g06_VC_keep (FT and FV without s3 / s8, write set of two intervals).
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b6.
Import ListNotations.
Open Scope Z_scope.

(* An exit of the opens_record chain to 0x13a80: nothing stored, s3 kept. *)
Ltac g06_exit :=
  apply evt_done; do 19 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|];
  split; [intros X; discriminate X | intros _; split; reflexivity].

(* A byte compare of the chain (bne / bnez against k): equal falls through, different exits. *)
Ltac g06_ne b k :=
  let E := fresh "E" in
  destruct (bv_unsigned b =? k) eqn:E;
  rewrite (b6_eqz b k) by lia; rewrite E; cbn [negb andb]; [ | g06_exit].

(* bv_unsigned of the literal words of the memcpy call (a1 = Φ + 27, a0 = sp + 40, a2 = Φ[26]). *)
Ltac g06_u :=
  unfold zxb;
  repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (MState.unsigned_lit z) by lia end);
  rewrite ?Z.add_0_r.
Ltac g06_uh H :=
  unfold zxb in H;
  repeat (match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (MState.unsigned_lit z) in H by lia end);
  rewrite ?Z.add_0_r in H.

Lemma g06_main : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (so bg : bool)
         (b16 b17 b18 b19 b22 b23 b24 b25 b26 : byte) (body j16 : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 (phi + 18) ->
    s1 = Z_to_bv 64 (b2z so) -> s2 = Z_to_bv 64 (b2z bg) -> (so = true -> bg = true) ->
    0 <= phi -> phi + 50 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m ->
    (so = true ->
       ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] /\ ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] /\
       ov_read_bytes rsegs m (wa (phi + 18)) 1 = Some [b18] /\ ov_read_bytes rsegs m (wa (phi + 19)) 1 = Some [b19] /\
       ov_read_bytes rsegs m (wa (phi + 22)) 1 = Some [b22] /\ ov_read_bytes rsegs m (wa (phi + 23)) 1 = Some [b23] /\
       ov_read_bytes rsegs m (wa (phi + 24)) 1 = Some [b24] /\ ov_read_bytes rsegs m (wa (phi + 25)) 1 = Some [b25] /\
       ov_read_bytes rsegs m (wa (phi + 26)) 1 = Some [b26] /\
       (1 <= bv_unsigned b26 <= 22 -> length body = Z.to_nat (bv_unsigned b26) /\ bytes_at rsegs m (phi + 27) body)) ->
    rw_cells rsegs m (spv + 16) [Cells.CB 8 j16] -> Frame.stk rsegs m (spv + 40) (spv + 76) ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (-7)) s3' s4 s5 s6 s7 s8' s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13a80) fc None m' (seg_rom rsegs) /\
         munch [(spv + 16, spv + 24); (spv + 40, spv + 76)] m m' /\ wmono rsegs m m' /\
         (b6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = true ->
            s3' = Z_to_bv 64 (bv_unsigned b26) /\
            bytes_at rsegs m' (spv + 16) (le8 (Z_to_bv 64 1)) /\ bytes_at rsegs m' (spv + 40) body) /\
         (b6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = false -> s3' = s3 /\ m' = m))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x139e8) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi so bg b16 b17 b18 b19 b22 b23 b24 b25 b26 body j16
    -> -> -> Hs1 Hs2 Hsb H1 H2 H3 MI HR C16 ST40.
  pose proof (munch_refl [(spv + 16, spv + 24); (spv + 40, spv + 76)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold b6_opn.
  destruct so.
  2:{ (* not sum_ok: 0x139ec to 0x13a7c *)
      destruct bg; cbn [b2z] in Hs1, Hs2; subst s1 s2; cbn [andb].
      all: step; step; if_true; step; g06_exit. }
  rewrite (Hsb eq_refl) in Hs2. cbn [b2z] in Hs1, Hs2. subst s1 s2. cbn [andb].
  destruct (HR eq_refl) as (R16 & R17 & R18 & R19 & R22 & R23 & R24 & R25 & R26 & HBD). clear HR.
  pose proof (RcLib.byte_range b26) as B26.
  step. step. if_false.
  step. step. step. step. g06_ne b16 205.
  step. step. step. g06_ne b17 234.
  step. step. step. g06_ne b18 4.
  step. step. step. g06_ne b19 1.
  step. step. g06_ne b22 0.
  step. step. step. g06_ne b23 2.
  step. step. g06_ne b24 0.
  step. step. step. g06_ne b25 254.
  step. step. step. step.
  rewrite b6_c26.
  destruct (1 <=? bv_unsigned b26) eqn:Ea; destruct (bv_unsigned b26 <=? 22) eqn:Eb; cbn [negb andb].
  2-4: g06_exit.
  (* opens_record holds: memcpy(sp+40, Φ+27, Φ[26]); have = 1; nb = Φ[26] (0x13a5c-0x13a78) *)
  apply Z.leb_le in Ea. apply Z.leb_le in Eb.
  destruct (HBD (conj Ea Eb)) as (Lb & Bb). clear HBD.
  destruct (sl_rw_of_stk m (spv + 40) (spv + 76) (spv + 40) (Z.to_nat (bv_unsigned b26)) ST40 ltac:(lia)
              ltac:(lia)) as (junk & Hj).
  step. step. step. step.
  eapply evt_cut.
  { eapply MC with (src := body) (junk := junk);
      [ g06_u; exact Bb | g06_u; exact Lb | g06_u; exact Hj | g06_u; lia | exact MI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              Ems & MUc & WMc & MIc & RWc & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13a6c)) with (Z_to_bv 64 0x13a6c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  g06_uh MUc. g06_uh RWc.
  pose proof (rw_cells_transport rsegs _ m m' _ _ C16 MUc WMc
                ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])) as C16'.
  clear C16. rename C16' into C16.
  assert (MU2 : munch [(spv + 16, spv + 24); (spv + 40, spv + 76)] m m').
  { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [Frame.outside].
    intros x (O1 & O2 & _). split; [lia | exact I]. }
  clear MU MUc. clear WM.
  step. step. step. step.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WMc|].
  split; [intros _ | intros X; discriminate X].
  split; [unfold zxb; rewrite ?(MState.unsigned_lit (bv_unsigned b26)) by lia; f_equal; lia|].
  split; [exact (b6_c8 _ _ _ C16) | exact (sl_rw_bytes _ _ _ _ RWc)].
Qed.

Lemma g06_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc spv phi : Z) (so bg : bool)
         (b16 b17 b18 b19 b22 b23 b24 b25 b26 : byte) (body j16 : list byte),
    (pc = 0x139e8 \/ (pc = 0x139e4 /\ (a0 = Z_to_bv 64 0 \/ a0 = Z_to_bv 64 1))) ->
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 (phi + 18) ->
    s1 = Z_to_bv 64 (b2z so) -> s2 = Z_to_bv 64 (b2z bg) -> (so = true -> bg = true) ->
    0 <= phi -> phi + 50 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m ->
    (so = true ->
       ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] /\ ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] /\
       ov_read_bytes rsegs m (wa (phi + 18)) 1 = Some [b18] /\ ov_read_bytes rsegs m (wa (phi + 19)) 1 = Some [b19] /\
       ov_read_bytes rsegs m (wa (phi + 22)) 1 = Some [b22] /\ ov_read_bytes rsegs m (wa (phi + 23)) 1 = Some [b23] /\
       ov_read_bytes rsegs m (wa (phi + 24)) 1 = Some [b24] /\ ov_read_bytes rsegs m (wa (phi + 25)) 1 = Some [b25] /\
       ov_read_bytes rsegs m (wa (phi + 26)) 1 = Some [b26] /\
       (1 <= bv_unsigned b26 <= 22 -> length body = Z.to_nat (bv_unsigned b26) /\ bytes_at rsegs m (phi + 27) body)) ->
    rw_cells rsegs m (spv + 16) [Cells.CB 8 j16] -> Frame.stk rsegs m (spv + 40) (spv + 76) ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 (-7)) s3' s4 s5 s6 s7 s8' s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13a80) fc None m' (seg_rom rsegs) /\
         munch [(spv + 16, spv + 24); (spv + 40, spv + 76)] m m' /\ wmono rsegs m m' /\
         (b6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = true ->
            s3' = Z_to_bv 64 (bv_unsigned b26) /\
            bytes_at rsegs m' (spv + 16) (le8 (Z_to_bv 64 1)) /\ bytes_at rsegs m' (spv + 40) body) /\
         (b6_opn so b16 b17 b18 b19 b22 b23 b24 b25 b26 = false -> s3' = s3 /\ m' = m))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pc spv phi so bg b16 b17 b18 b19 b22 b23 b24 b25 b26 body j16
    Hpc Hsp Hs5 Hs9 Hs1 Hs2 Hsb H1 H2 H3 MI HR C16 ST40.
  destruct Hpc as [-> | [-> [-> | ->]]]; [| step; if_false | step; if_false].
  all: eapply (g06_main MC); eassumption.
Qed.

(* The registers G06 keeps that FT and FV read (s3 and s8 apart: an opening FIRST sets both). *)
Definition g06_kT (regs regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 8 = YK11.getr regs 8 /\ YK11.getr regs' 9 = YK11.getr regs 9 /\
  YK11.getr regs' 20 = YK11.getr regs 20 /\ YK11.getr regs' 21 = YK11.getr regs 21 /\
  YK11.getr regs' 22 = YK11.getr regs 22 /\ YK11.getr regs' 23 = YK11.getr regs 23 /\
  YK11.getr regs' 25 = YK11.getr regs 25 /\ YK11.getr regs' 26 = YK11.getr regs 26 /\
  YK11.getr regs' 27 = YK11.getr regs 27.

Lemma g06_FT_keep : forall g j phi regs regs' m m' W,
  FT g j phi regs m -> g06_kT regs regs' -> munch W m m' ->
  disjoint_from W phi (t_len (g_in g) j) -> disjoint_from W (spk g 32) 8 -> disjoint_from W (spk g 76) 6 ->
  disjoint_from W (spk g 8) 8 -> FT g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' W (Hj & H26 & (H27 & H32 & H20) & H21 & HPhi & HOUR & HM7)
    (E8 & E9 & E20 & E21 & E22 & E23 & E25 & E26 & E27) MU Dp D32 D76 D8.
  unfold FT, FC, rg in *. rewrite E26, E27, E20, E21.
  split; [exact Hj|]. split; [exact H26|].
  split; [split; [exact H27|]; split; [|exact H20]|].
  { unfold q64 in *. apply (bytes_at_transport rsegs W m m' _ _ H32 MU). rewrite length_le8. exact D32. }
  split; [exact H21|]. split.
  - apply (bytes_at_transport rsegs W m m' _ _ HPhi MU). rewrite b6_phi_len.
    pose proof (b6_len_range (g_in g) j). rewrite Z2Nat.id by lia. exact Dp.
  - split.
    + unfold OURb in *. apply (bytes_at_transport rsegs W m m' _ _ HOUR MU). rewrite OUR_length. exact D76.
    + unfold M7, q64 in *. apply (bytes_at_transport rsegs W m m' _ _ HM7 MU). rewrite length_le8. exact D8.
Qed.

Lemma g06_VC_keep : forall g j phi regs regs' m m' W,
  VC g j phi regs m -> g06_kT regs regs' -> munch W m m' ->
  disjoint_from W (spk g 24) 8 -> disjoint_from W (spk g 1752) 36 -> VC g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' W (H8 & H22 & HTF & HB)
    (E8 & E9 & E20 & E21 & E22 & E23 & E25 & E26 & E27) MU D24 DB.
  unfold VC, rg in *. rewrite E8, E22.
  split; [exact H8|]. split; [exact H22|].
  split; [unfold q64 in *; apply (bytes_at_transport rsegs W m m' _ _ HTF MU); rewrite length_le8; exact D24|].
  apply (bytes_at_transport rsegs W m m' _ _ HB MU). unfold t_B. rewrite RcParse.ctrlparse_length. exact DB.
Qed.

Ltac g06_dj := cbn [disjoint_from]; unfold spk, fsp, SLOT_FRAME in *; repeat split; try exact I; lia.

Section G06.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MC : memcpy_contract.

Lemma seg_G06 : forall j,
  Hat B APIf ra (Inv_K13a80_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K139e4_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K139e8_at B APIf ra empty) j.
Proof.
  intros j H50.
  assert (RUN : forall g phi L A regs mem md pc,
    (pc = 0x139e8 \/
     (pc = 0x139e4 /\ (YK11.getr regs 10 = Z_to_bv 64 0 \/ YK11.getr regs 10 = Z_to_bv 64 1))) ->
    FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
    Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
    GE g j phi regs mem ->
    SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) (Post B APIf ra g)).
  { intros g phi L A regs mem md pc Hpc HFR HP HGE.
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    destruct (b6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
    pose proof HGE as (HB & HI & HG & HS).
    pose proof HB as (HT & H7 & H9 & H0 & H2 & HC).
    pose proof HT as (Hj & H26 & HFC & H21 & HPhi & HOUR & HM7).
    pose proof HS as (H16q & H19 & HBody & HLen & HFI).
    unfold q64 in H16q.
    pose proof (b6_len_range (g_in g) j) as (Hl0 & _ & _).
    pose proof (b6_g_len (g_in g) j) as LG.
    unfold SLOT_K, SLOT_STACK, SL_TOP in *.
    assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
    pose proof (b6_rw_of (normalize rsegs mem) (g_S g - 65536) (g_S g) (spk g 16) _ ST
                  ltac:(unfold spk; lia) ltac:(rewrite length_le8; unfold spk; lia) (b6_norm mem _ _ HMI H16q)) as C16.
    rewrite length_le8 in C16.
    assert (ST40 : Frame.stk rsegs (normalize rsegs mem) (fsp g + 40) (fsp g + 76)).
    { destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros a Ha. apply S3. lia. }
    eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(fsp g + 16, fsp g + 24); (fsp g + 40, fsp g + 76)]);
      [exact HFR | exact HP | | | |].
    - intros x Hx O. apply (sl_fp1 g (fsp g + 16) (fsp g + 76) x); [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx |].
      intros O'. apply O. cbn [Frame.outside] in *. destruct O' as (O1 & _). split; [lia|]. split; [lia | exact I].
    - rewrite sl_mkR_of.
      apply (g06_evt MC) with (spv := fsp g) (phi := phi) (so := t_sum_ok (g_in g) j) (bg := t_big (g_in g) j)
        (b16 := nth 16 (t_g (g_in g) j) (Z_to_bv 8 0)) (b17 := nth 17 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b18 := nth 18 (t_g (g_in g) j) (Z_to_bv 8 0)) (b19 := nth 19 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b22 := nth 22 (t_g (g_in g) j) (Z_to_bv 8 0)) (b23 := nth 23 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b24 := nth 24 (t_g (g_in g) j) (Z_to_bv 8 0)) (b25 := nth 25 (t_g (g_in g) j) (Z_to_bv 8 0))
        (b26 := nth 26 (t_g (g_in g) j) (Z_to_bv 8 0))
        (body := fg_body (t_g (g_in g) j)) (j16 := le8 (Z_to_bv 64 (fs_have (fst_at (g_in g) j)))).
      + exact Hpc.
      + exact Hsp.
      + exact H21.
      + exact H9.
      + exact H0.
      + exact H2.
      + intros Hso. unfold t_sum_ok in Hso. apply andb_prop in Hso. exact (proj1 Hso).
      + lia.
      + lia.
      + lia.
      + exact (mem_inv_normalize rsegs mem).
      + intros Hso.
        assert (Hl : 50 <= t_len (g_in g) j).
        { unfold t_sum_ok, t_big in Hso. apply andb_prop in Hso as (Hb & _). apply Z.leb_le in Hb. exact Hb. }
        pose proof (b6_norm mem _ _ HMI (b6_ba_g mem phi (g_in g) j HPhi Hl)) as HG50.
        split; [exact (RcLib.rd_byte rsegs _ phi _ 16 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 17 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 18 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 19 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 22 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 23 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 24 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 25 HG50 ltac:(lia))|].
        split; [exact (RcLib.rd_byte rsegs _ phi _ 26 HG50 ltac:(lia))|].
        intros Hr. change (bv_unsigned (nth 26 (t_g (g_in g) j) (Z_to_bv 8 0))) with (fg_n (t_g (g_in g) j)) in Hr |- *.
        split; [unfold fg_body; apply b6_bsl_len; lia|].
        pose proof (b6_ba_sub _ phi _ 27 (Z.to_nat (fg_n (t_g (g_in g) j))) HG50 ltac:(lia)) as HBy.
        change (Z.of_nat 27) with 27 in HBy. exact HBy.
      + exact C16.
      + exact ST40.
    - intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s8' & t3' & t4' & t5' &
                 t6' & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity | split; reflexivity].
    - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
      destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s8' & t3' & t4' &
                      t5' & t6' & m'' & HE & _ & _ & Hop & Hno).
      injection HE; intros; subst.
      assert (K : g06_kT regs regs') by (unfold g06_kT; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
      assert (E18 : YK11.getr regs' 18 = Z_to_bv 64 (-7)) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      assert (E19 : YK11.getr regs' 19 = s3') by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      pose proof K as (E8 & E9 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
      destruct (b6_inv (g_in g) (S j)) as (LI1 & _ & _).
      destruct (b6_lens (g_in g) j) as (_ & LF & _).
      pose proof (b6_FI_S (g_in g) j HFI) as HFI'.
      rewrite (b6_opn_eq (g_in g) j) in Hop, Hno.
      apply H50. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact (g06_FT_keep g j phi regs regs' mem m' _ HT K MU ltac:(g06_dj) ltac:(g06_dj) ltac:(g06_dj)
                       ltac:(g06_dj))|].
      split; [unfold V7, rg in *; rewrite E23; exact H7|].
      split; [unfold V9, rg in *; rewrite E25; exact H9|].
      split; [unfold V0, rg in *; rewrite E9; exact H0|].
      split; [exact E18|].
      split; [exact (g06_VC_keep g j phi regs regs' mem m' _ HC K MU ltac:(g06_dj) ltac:(g06_dj))|].
      split.
      { destruct HI as (HIb & HIok). split; [|exact HIok]. unfold IDB in *.
        apply (bytes_at_transport rsegs _ mem m' _ _ HIb MU). rewrite LI1. g06_dj. }
      split.
      { unfold FGj. rewrite b6_tFG_S. destruct HG as (HGb & HGok). split; [|exact HGok]. unfold FGB in *.
        apply (bytes_at_transport rsegs _ mem m' _ _ HGb MU). rewrite LF. g06_dj. }
      unfold FSj, FSb. rewrite (b6_fs_S (g_in g) j) in HFI' |- *. revert HFI'.
      destruct (f_opens (t_len (g_in g) j) (t_g (g_in g) j)) eqn:Eo;
        cbn [fs_have fs_nb fs_body]; intros HFI'; unfold q64, rg.
      + destruct (Hop ltac:(first [exact Eo | reflexivity])) as (Q19 & Q16 & Q40).
        unfold f_opens in Eo. apply andb_prop in Eo as (Efr & _). destruct (b6_fr_n _ _ Efr) as (_ & Hn).
        split; [exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) Q16)|].
        split; [rewrite E19, Q19; reflexivity|].
        split; [exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) Q40)|].
        split; [|exact HFI'].
        unfold fg_body. rewrite b6_bsl_len by (try rewrite LG; unfold fg_n in *; lia). unfold fg_n in *. lia.
      + destruct (Hno ltac:(first [exact Eo | reflexivity])) as (Q19 & Q). rewrite Q in Hrel.
        split; [exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) (b6_norm mem _ _ HMI H16q))|].
        split; [rewrite E19, Q19; exact H19|].
        split; [exact (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel) (b6_norm mem _ _ HMI HBody))|].
        split; [exact HLen | exact HFI']. }
  split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGE & _ & H10).
    assert (Ha : YK11.getr regs 10 = Z_to_bv 64 0 \/ YK11.getr regs 10 = Z_to_bv 64 1).
    { unfold rg in H10. rewrite H10.
      match goal with |- context [fst (RcIdentModel.ING ?x ?y ?z)] =>
        destruct (RcIdentModel.ING_ret x y z) as [E | E]; rewrite E; [left | right]; reflexivity end. }
    exact (RUN g phi L A regs mem md 0x139e4 (or_intror (conj eq_refl Ha)) HFR HP HGE).
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGE).
    exact (RUN g phi L A regs mem md 0x139e8 (or_introl eq_refl) HFR HP HGE).
Qed.

End G06.
