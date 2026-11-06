(* Segment G05 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13950, 0x139e0], K13950 -> K139e4 (the CLOSE record's
   sum loop, the P4l address check through `first`, reac_identity_ingest on the payload in frag).
   libreac v1.9.0 (table 5a S_G05, CHANGED: branch-target, code, new-insert, operand, register; NEW 0x13950-0x139e0
   from the v1.9.0 listing): the sum loop runs over frag + 15 = sp+97 (v1.8 sp+81) with nb copied to a6
   (0x13960 `mv a6,s3`, new); `first.have` is [sp+16] (0x1397c `ld a0,16(sp)`, 0x13980 `beqz a0`); the address bytes
   are v1.9's inlined joined_byte(&first, block, 9 / 10) (fuzz/fuzz_ctrl.c v1.9.0:251-254): body[9] = [sp+49] when
   9 < nb, else block[18 - nb] = s6 + 18 - nb (0x13984-0x139a0), body[10] = [sp+50] when 10 < nb, else
   s6 + 19 - nb (0x139a4-0x139c0); (b9 << 8) | b10 against the u16 at sp+1750 (0x139c4-0x139d8); ingest(sp+154,
   addr, sp+101, pll). The address is fg_addr by SlotModel.fg_addr_joined (Tac_b6.b6_P4l). v1.8's lemma g05_addr
   (the 48-bit masking of the old sequence) is gone; g05_pick9 / g05_pick10 are new. rule 24: no function
   proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag SlotModel SlotInv reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b6.
Import ListNotations.
Open Scope Z_scope.


Section Loop.
Variables (ra gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv pll : Z) (bs : list byte)
  (Q : machine_state -> Prop).
Hypothesis Hs : 0 <= spv.
Hypothesis Hsp : spv + 1936 <= 2 ^ 64.
Hypothesis Hp : 1 <= pll <= 51.
Hypothesis Hlen : length bs = Z.to_nat (pll + 5).
Hypothesis HB : bytes_at rsegs m (spv + 97) bs.
Hypothesis HK : forall a5' : word,
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (psum bs (length bs)))
                       (Z_to_bv 64 (spv + 102 + pll)) a2 a3 (Z_to_bv 64 (spv + 102 + pll)) a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13974) fc None m (seg_rom rsegs)).

(* The record sum loop 0x13964-0x13970 over frag[15 .. 20 + pll) (a6 = nb is only carried). *)
Lemma g05_loop : forall n i a5, (i + n = length bs)%nat -> (0 < n)%nat ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (psum bs i))
                       (Z_to_bv 64 (spv + 102 + pll)) a2 a3 (Z_to_bv 64 (spv + 97 + Z.of_nat i)) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13964) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros i a5 Hin Hn; [lia|].
  pose proof (RcLib.rd_byte rsegs m (spv + 97) bs i HB ltac:(lia)) as RD.
  pose proof (RcLib.psum_range bs i) as PR.
  step. step. step. step.
  rewrite RcLib.psum_S_zxb. rewrite b6_eqb by lia.
  destruct n as [|n].
  - if_false.
    replace (S i) with (length bs) by lia.
    replace (spv + 97 + Z.of_nat i + 1) with (spv + 102 + pll) by lia.
    apply HK.
  - if_true.
    replace (spv + 97 + Z.of_nat i + 1) with (spv + 97 + Z.of_nat (S i)) by lia.
    apply (IH (S i)); lia.
Qed.
End Loop.

(* The zero-extended 32-bit index of the inlined joined_byte (subw; slli 32; srli 32; add): the register value as
   a plain sum. *)
Ltac g05_zs :=
  repeat (first
    [ rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia)
    | match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (MState.unsigned_lit z) by lia end
    | rewrite Z.shiftl_mul_pow2 by lia
    | rewrite Z.shiftr_div_pow2 by lia
    | rewrite Z.div_mul by lia ]);
  f_equal; lia.

(* 0x13984-0x139a0: a0 = &joined_byte(&first, block, 9): sp+49 (body[9]) when 9 < nb, else s6 + 18 - nb. *)
Lemma g05_pick9 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (spv s6v nb : Z),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 s6v -> a6 = Z_to_bv 64 nb ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= s6v -> s6v + 50 <= 2 ^ 64 -> 1 <= nb <= 22 ->
    (forall a0' a1' : word, a0' = Z_to_bv 64 (if 9 <? nb then spv + 49 else s6v + 18 - nb) ->
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x139a4) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13984) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q spv s6v nb -> -> -> Hs Hsp H6 H6b Hnb HK.
  step. step. step. rewrite b6_ltu by lia.
  destruct (Z.ltb_spec 9 nb) as [Hgt | Hle].
  - try if_true. apply HK. try rewrite (proj2 (Z.ltb_lt 9 nb) Hgt). cbv beta iota.
    first [reflexivity | f_equal; lia].
  - try if_false. step. step. step. step. step.
    apply HK. try rewrite (proj2 (Z.ltb_ge 9 nb) Hle). cbv beta iota. g05_zs.
Qed.

(* 0x139a4-0x139c0: a1 = &joined_byte(&first, block, 10): sp+50 (body[10]) when 10 < nb, else s6 + 19 - nb. *)
Lemma g05_pick10 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (spv s6v nb : Z),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 s6v -> a6 = Z_to_bv 64 nb ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= s6v -> s6v + 50 <= 2 ^ 64 -> 1 <= nb <= 22 ->
    (forall a1' a4' : word, a1' = Z_to_bv 64 (if 10 <? nb then spv + 50 else s6v + 19 - nb) ->
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4' a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x139c4) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x139a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q spv s6v nb -> -> -> Hs Hsp H6 H6b Hnb HK.
  step. step. step. rewrite b6_ltu by lia.
  destruct (Z.ltb_spec 10 nb) as [Hgt | Hle].
  - try if_true. apply HK. try rewrite (proj2 (Z.ltb_lt 10 nb) Hgt). cbv beta iota.
    first [reflexivity | f_equal; lia].
  - try if_false. step. step. step. step. step.
    apply HK. try rewrite (proj2 (Z.ltb_ge 10 nb) Hle). cbv beta iota. g05_zs.
Qed.

(* 0x139c4-0x139e0: the two address bytes, (b9 << 8) | b10 against the u16 at sp+1750, then
   reac_identity_ingest(sp+154, addr, sp+101, pll). *)
Lemma g05_tail : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv pll p9 p10 addr : Z) (pb idb : list byte)
         (b9 b10 : byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 p9 -> a1 = Z_to_bv 64 p10 -> a2 = Z_to_bv 64 (spv + 101) ->
    a3 = Z_to_bv 64 pll ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 2 = 0 -> 1 <= pll <= 51 ->
    ov_read_bytes rsegs m (wa p9) 1 = Some [b9] -> ov_read_bytes rsegs m (wa p10) 1 = Some [b10] ->
    ov_read_bytes rsegs m (wa (spv + 1750)) 2 = Some (le2 (Z_to_bv 64 addr)) ->
    0 <= addr < 65536 -> addr = 256 * bv_unsigned b9 + bv_unsigned b10 ->
    rw_cells rsegs m (spv + 154) [Cells.CB 38 idb] -> length pb = Z.to_nat pll -> bytes_at rsegs m (spv + 101) pb ->
    evt rsegs
      (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x139e4) sp gp tp t0' t1' t2 s0 s1
                       (Z_to_bv 64 (fst (RcIdentModel.ING idb addr pb))) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x139e4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 154, spv + 192)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 154) (snd (RcIdentModel.ING idb addr pb)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x139c4) fc None m (seg_rom rsegs)).
Proof.
  intros ING ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv pll p9 p10 addr pb idb b9 b10 -> -> -> -> -> Hs Hsp Hev Hp R9 R10 R1750 Had Haddr HC Hpb HPB.
  pose proof (RcLib.byte_range b9) as B9. pose proof (RcLib.byte_range b10) as B10.
  step. step. step. step. step. step.
  rewrite b6_orshl. rewrite b6_zx16 by lia. rewrite b6_eqb by lia.
  if_false.
  step. step.
  assert (Href : ingest_refused (spv + 154) (spv + 101) pll = false).
  { unfold ingest_refused. apply orb_false_iff. split; [apply Z.eqb_neq; lia|].
    apply andb_false_iff. right. apply Z.eqb_neq. lia. }
  eapply evt_cut.
  { eapply ING with (id := spv + 154) (ad := addr) (p := spv + 101) (len := pll) (idb := idb) (pb := pb);
      [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | lia
      | intros _; split; [rewrite Zplus_mod, Hev; reflexivity | exact HC] | exact Hpb
      | intros _ _; exact HPB | intros _ _ _; left; lia]. }
  intros ms' (t0' & t1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MUc & WMc & _ & _ & Hz).
  subst ms'. specialize (Hz Href). unfold ingest_ret. rewrite Href.
  replace (spv + 154 + 38) with (spv + 192) in MUc by lia.
  replace (ret_pc (Z_to_bv 64 0x139e4)) with (Z_to_bv 64 0x139e4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', a1', a2', a3', a4', a5', a6', a7', m'.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|].
  exact (sl_rw_bytes _ _ _ _ Hz).
Qed.

Lemma g05_evt : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv pll s6v nb addr : Z)
         (bs pb idb : list byte) (b9 b10 : byte),
    sp = Z_to_bv 64 spv -> a2 = Z_to_bv 64 (spv + 101) -> a3 = Z_to_bv 64 pll ->
    s3 = Z_to_bv 64 nb -> s6 = Z_to_bv 64 s6v ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 2 = 0 -> 1 <= pll <= 51 ->
    0 <= s6v -> s6v + 50 <= 2 ^ 64 -> 1 <= nb <= 22 ->
    length bs = Z.to_nat (pll + 5) -> bytes_at rsegs m (spv + 97) bs -> psum bs (length bs) mod 128 = 0 ->
    ov_read_bytes rsegs m (wa (spv + 16)) 8 = Some (le8 (Z_to_bv 64 1)) ->
    ov_read_bytes rsegs m (wa (if 9 <? nb then spv + 49 else s6v + 18 - nb)) 1 = Some [b9] ->
    ov_read_bytes rsegs m (wa (if 10 <? nb then spv + 50 else s6v + 19 - nb)) 1 = Some [b10] ->
    ov_read_bytes rsegs m (wa (spv + 1750)) 2 = Some (le2 (Z_to_bv 64 addr)) ->
    0 <= addr < 65536 -> addr = 256 * bv_unsigned b9 + bv_unsigned b10 ->
    rw_cells rsegs m (spv + 154) [Cells.CB 38 idb] -> length pb = Z.to_nat pll -> bytes_at rsegs m (spv + 101) pb ->
    evt rsegs
      (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x139e4) sp gp tp t0' t1' t2 s0 s1
                       (Z_to_bv 64 (fst (RcIdentModel.ING idb addr pb))) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x139e4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 154, spv + 192)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 154) (snd (RcIdentModel.ING idb addr pb)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13950) fc None m (seg_rom rsegs)).
Proof.
  intros ING ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv pll s6v nb addr bs pb idb b9 b10 -> -> -> -> -> Hs Hsp Hev Hp H6 H6b Hnb Hlen HB HS
    R16 R9 R10 R1750 Had Haddr HC Hpb HPB.
  step. step. step. step. step.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (psum bs 0)).
  replace (spv + 97) with (spv + 97 + Z.of_nat 0) by lia.
  eapply g05_loop with (n := length bs) (i := 0%nat);
    [exact Hs | exact Hsp | exact Hp | exact Hlen | exact HB | | lia | lia].
  intros a5'.
  pose proof (RcLib.psum_range bs (length bs)) as PR.
  step. step.
  rewrite (MState.unsigned_lit (psum bs (length bs))) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128. rewrite HS.
  if_false.
  step. step. if_false.
  eapply g05_pick9 with (spv := spv) (s6v := s6v) (nb := nb);
    [reflexivity | reflexivity | first [reflexivity | f_equal; lia] | lia | lia | lia | lia | lia |].
  intros a0' a1' E0.
  eapply g05_pick10 with (spv := spv) (s6v := s6v) (nb := nb);
    [reflexivity | reflexivity | first [reflexivity | f_equal; lia] | lia | lia | lia | lia | lia |].
  intros a1'' a4' E1.
  eapply (g05_tail ING) with (p9 := if 9 <? nb then spv + 49 else s6v + 18 - nb)
    (p10 := if 10 <? nb then spv + 50 else s6v + 19 - nb) (addr := addr) (b9 := b9) (b10 := b10);
    [reflexivity | exact E0 | exact E1 | reflexivity | reflexivity | exact Hs | exact Hsp | exact Hev | exact Hp
    | exact R9 | exact R10 | exact R1750 | exact Had | exact Haddr | exact HC | exact Hpb | exact HPB].
Qed.

Section G05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis ING : reac_identity_ingest_contract.
Hypothesis INGK : reac_identity_ingest_id_ok_kept.

Lemma seg_G05 : forall j,
  Hat B APIf ra (Inv_K139e4_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13950_at B APIf ra empty) j.
Proof.
  intros j H9e4 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H24 & Hrf & H12 & H13).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b6_phi_rng B APIf ra empty _ _ _ _ _ _ _ _ HFR HP) as (Hph & Hph2).
  pose proof HGF as (HB & HI & HG & HS & _ & Hrs). destruct (Hrs Hrf) as (Hadr & _ & _).
  pose proof HB as ((_ & _ & _ & _ & Hphi & _) & (_ & _ & _ & _ & (_ & H22 & _))).
  destruct (b6_close_facts (g_in g) j Hrf) as (HT & _ & Hl & _ & LF & HR).
  pose proof Hrf as Hrf'. unfold t_rf in Hrf'. destruct (b6_close _ _ _ Hrf') as (_ & Efr & _).
  destruct (b6_fr_n _ _ Efr) as (H50 & _).
  assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact H50).
  pose proof HS as (H16f & H19 & HBody & HLen & HFI).
  destruct (b6_P4l (g_in g) j Hrf HFI) as (Hhv & Hnb & Haddr).
  destruct (b6_lens (g_in g) j) as (LI & _ & _).
  pose proof HG as (HFG & _). pose proof HI as (HID & HIok). unfold FGB, IDB in HFG, HID.
  pose proof (b6_ba_g mem phi (g_in g) j Hphi H50) as HGG.
  pose proof (b6_g_len (g_in g) j) as LG.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Hf : fsp g = g_S g - 1936) by (unfold fsp, SLOT_FRAME; reflexivity).
  set (st := t_FG (g_in g) j) in *. set (gg := t_g (g_in g) j) in *. set (FGf := t_FGf (g_in g) j) in *.
  set (s := fst_at (g_in g) j) in *.
  set (pll := f_pll st gg).
  assert (Hpll : pll = fg_T st gg - 13) by reflexivity.
  (* the CLOSE record's bytes frag[15 ..] (the sum loop) and the payload frag[19 ..] *)
  pose proof (b6_ba_sub mem (spk g 82) FGf 15 (Z.to_nat (fg_T st gg - 8)) HFG ltac:(rewrite LF; lia)) as HBS.
  replace (spk g 82 + Z.of_nat 15) with (fsp g + 97) in HBS by (unfold spk; lia).
  pose proof (b6_ba_sub mem (spk g 82) FGf 19 (Z.to_nat pll) HFG ltac:(rewrite LF; lia)) as HPB.
  replace (spk g 82 + Z.of_nat 19) with (fsp g + 101) in HPB by (unfold spk; lia).
  assert (LBS : length (bsl FGf 15 (fg_T st gg - 8)) = Z.to_nat (pll + 5)) by (rewrite b6_bsl_len; lia).
  assert (LPB : length (bsl FGf 19 pll) = Z.to_nat pll) by (rewrite b6_bsl_len; lia).
  assert (Had : 0 <= fg_addr st gg < 65536).
  { unfold fg_addr. pose proof (b6_bat_range (fg_join st gg) 17). pose proof (b6_bat_range (fg_join st gg) 18). lia. }
  (* joined_byte(&first, block, 9 / 10): body[i] at sp+40+i when i < nb, else Φ[27 + i - nb] at s6 + 9 + i - nb *)
  assert (R9 : ov_read_bytes rsegs (normalize rsegs mem)
                 (wa (if 9 <? fs_nb s then fsp g + 49 else phi + 18 + 18 - fs_nb s)) 1 =
               Some [if 9 <? fs_nb s then nth (Z.to_nat 9) (fs_body s) (Z_to_bv 8 0)
                     else nth (Z.to_nat (27 + 9 - fs_nb s)) gg (Z_to_bv 8 0)]).
  { destruct (Z.ltb_spec 9 (fs_nb s)) as [Hgt | Hle].
    - pose proof (RcLib.rd_byte rsegs (normalize rsegs mem) (spk g 40) (fs_body s) 9 (b6_norm mem _ _ HMI HBody)
                    ltac:(lia)) as R.
      change (Z.to_nat 9) with 9%nat. replace (fsp g + 49) with (spk g 40 + Z.of_nat 9) by (unfold spk; lia).
      exact R.
    - pose proof (RcLib.rd_byte rsegs (normalize rsegs mem) phi gg (Z.to_nat (27 + 9 - fs_nb s))
                    (b6_norm mem _ _ HMI HGG) ltac:(rewrite LG; lia)) as R.
      rewrite Z2Nat.id in R by lia. replace (phi + 18 + 18 - fs_nb s) with (phi + (27 + 9 - fs_nb s)) by lia.
      exact R. }
  assert (R10 : ov_read_bytes rsegs (normalize rsegs mem)
                  (wa (if 10 <? fs_nb s then fsp g + 50 else phi + 18 + 19 - fs_nb s)) 1 =
                Some [if 10 <? fs_nb s then nth (Z.to_nat 10) (fs_body s) (Z_to_bv 8 0)
                      else nth (Z.to_nat (27 + 10 - fs_nb s)) gg (Z_to_bv 8 0)]).
  { destruct (Z.ltb_spec 10 (fs_nb s)) as [Hgt | Hle].
    - pose proof (RcLib.rd_byte rsegs (normalize rsegs mem) (spk g 40) (fs_body s) 10 (b6_norm mem _ _ HMI HBody)
                    ltac:(lia)) as R.
      change (Z.to_nat 10) with 10%nat. replace (fsp g + 50) with (spk g 40 + Z.of_nat 10) by (unfold spk; lia).
      exact R.
    - pose proof (RcLib.rd_byte rsegs (normalize rsegs mem) phi gg (Z.to_nat (27 + 10 - fs_nb s))
                    (b6_norm mem _ _ HMI HGG) ltac:(rewrite LG; lia)) as R.
      rewrite Z2Nat.id in R by lia. replace (phi + 18 + 19 - fs_nb s) with (phi + (27 + 10 - fs_nb s)) by lia.
      exact R. }
  assert (EA : fg_addr st gg =
    256 * bv_unsigned (if 9 <? fs_nb s then nth (Z.to_nat 9) (fs_body s) (Z_to_bv 8 0)
                       else nth (Z.to_nat (27 + 9 - fs_nb s)) gg (Z_to_bv 8 0)) +
    bv_unsigned (if 10 <? fs_nb s then nth (Z.to_nat 10) (fs_body s) (Z_to_bv 8 0)
                 else nth (Z.to_nat (27 + 10 - fs_nb s)) gg (Z_to_bv 8 0))).
  { rewrite Haddr. unfold joined_byte, bat.
    destruct (9 <? fs_nb s); destruct (10 <? fs_nb s); reflexivity. }
  pose proof (b6_ovr _ _ _ (b6_norm mem _ _ HMI Hadr)) as R1750. rewrite length_le2 in R1750.
  pose proof (b6_rw_of (normalize rsegs mem) (g_S g - 65536) (g_S g) (spk g 154) (t_IDr (g_in g) j) ST
                ltac:(unfold spk; lia) ltac:(rewrite LI; unfold spk; lia) (b6_norm mem _ _ HMI HID)) as HC.
  rewrite LI in HC.
  eapply (b6_mid B APIf ra empty FF g _ L A regs mem md _ [(fsp g + 154, fsp g + 192)]); [exact HFR | exact HP | | | |].
  - intros x Hx O. apply (sl_fp1 g (fsp g + 154) (fsp g + 192) x); [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - rewrite sl_mkR_of.
    apply (g05_evt ING) with (spv := fsp g) (pll := pll) (s6v := phi + 18) (nb := fs_nb s)
      (bs := bsl FGf 15 (fg_T st gg - 8)) (addr := fg_addr st gg) (pb := bsl FGf 19 pll) (idb := t_IDr (g_in g) j)
      (b9 := if 9 <? fs_nb s then nth (Z.to_nat 9) (fs_body s) (Z_to_bv 8 0)
             else nth (Z.to_nat (27 + 9 - fs_nb s)) gg (Z_to_bv 8 0))
      (b10 := if 10 <? fs_nb s then nth (Z.to_nat 10) (fs_body s) (Z_to_bv 8 0)
              else nth (Z.to_nat (27 + 10 - fs_nb s)) gg (Z_to_bv 8 0)).
    + exact Hsp.
    + exact H12.
    + exact H13.
    + exact H19.
    + unfold rg in H22. rewrite H22, Hbig. reflexivity.
    + lia.
    + lia.
    + clear -H16. Z.div_mod_to_equations. lia.
    + lia.
    + lia.
    + lia.
    + exact Hnb.
    + exact LBS.
    + exact (b6_norm mem _ _ HMI HBS).
    + unfold recsum in HR. rewrite LBS. replace (Z.to_nat (pll + 5)) with (length (bsl FGf 15 (fg_T st gg - 8))) by exact LBS.
      exact HR.
    + apply b6_q64_ovr. apply b6_q64_norm; [exact HMI|]. rewrite <- Hhv. exact H16f.
    + exact R9.
    + exact R10.
    + exact R1750.
    + exact Had.
    + exact EA.
    + exact HC.
    + exact LPB.
    + exact (b6_norm mem _ _ HMI HPB).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity | split; reflexivity].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ).
    injection HE; intros; subst.
    assert (K : b6_kS regs regs') by (unfold b6_kS; rewrite !(sl_getr_eqv _ _ _ Hx); repeat split).
    assert (E18 : YK11.getr regs' 18 = YK11.getr regs 18) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (AV : b6_av g phi (t_len (g_in g) j) (fsp g + 154) (fsp g + 192)) by (unfold b6_av, b6_out, spk; lia).
    apply H9e4. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [|split; [|split]]|].
    + exact (b6_FB_keep g j phi regs regs' mem m' _ _ HB K E18 MU AV).
    + unfold IDj, IDb, IDB. rewrite (b6_tID_S1 (g_in g) j Hrf).
      split; [exact (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel) HZ)|].
      exact (INGK _ _ _ LI HIok).
    + exact (b6_FGb_keep g _ mem m' _ _ HG ltac:(exact LF) MU ltac:(unfold b6_out, spk; lia)).
    + exact (b6_FSb_keep g _ _ regs regs' mem m' _ _ HS (proj1 (proj2 (proj2 K))) MU
               ltac:(pose proof (b6_nb_range (g_in g) j); lia) ltac:(unfold b6_out, spk; lia)).
    + split; [exact Hrf|]. unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G05.
