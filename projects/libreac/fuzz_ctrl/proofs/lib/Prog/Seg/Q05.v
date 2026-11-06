(* Segment Q05 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13bd8, 0x13c3c], K13bd8 -> K13c40. The port-slot loop
   (head 0x13bf0, 12 turns, C5.5) counts the codes {00, 02}, {01}, {03} among blk[8 .. 20) and keeps the first code
   >= 4 (known_slot(c) is c <u 4, AF4). *)
(* libreac v1.9.0 (IDENTICAL, segment table 5a S_Q05): v1.8 [0x13ba8, 0x13c0c] K13ba8 -> K13c10, loop head 0x13bc0,
   pcs only; VC -> VCm in EQ (SlotInv.v). Statement kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* ---- One code c of the loop (AF4): the three counters and the first unknown code ---- *)

Lemma q05_in : forall c : byte,
  bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (zxb c)) 253)) 1) =
  if RcLeaf.is_in (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite b7_uzxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land u 253)) 1))
                                      (if RcLeaf.is_in u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_out : forall c : byte,
  bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -1)) 1) = if RcLeaf.is_out (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite b7_uzxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 (u + -1)) 1))
                                      (if RcLeaf.is_out u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_emp : forall c : byte,
  bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -3)) 1) = if is_empty (bv_unsigned c) then 1 else 0.
Proof.
  intros c. rewrite b7_uzxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 (u + -3)) 1))
                                      (if is_empty u then 1 else 0)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_snez : forall f, 0 <= f < 256 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))) =
  if f =? 0 then 0 else 1.
Proof.
  intros f R.
  pose proof (b7_all (fun f => Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0)
                                  (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                                      (if f =? 0 then 0 else 1)) ltac:(vm_compute; reflexivity) f R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma q05_known : forall c : byte,
  bv_unsigned (v_sltiu (zxb c) 4) = if 4 <=? bv_unsigned c then 0 else 1.
Proof.
  intros c. unfold zxb. pose proof (b7_byte_range c) as R. revert R. generalize (bv_unsigned c). intros u R.
  pose proof (b7_all (fun u => Z.eqb (bv_unsigned (v_sltiu (Z_to_bv 64 u) 4))
                                      (if 4 <=? u then 0 else 1)) ltac:(vm_compute; reflexivity) u R) as E.
  cbv beta in E. apply Z.eqb_eq in E. exact E.
Qed.

(* beqz t0 at 0x13c08 with t0 = (zext.b first != 0) | (c <u 4). *)
Lemma q05_br : forall f (c : byte), 0 <= f < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 f)) 255))))
                             (bv_unsigned (v_sltiu (zxb c) 4))))
         (Z_to_bv 64 0) = (f =? 0) && (4 <=? bv_unsigned c).
Proof.
  intros f c Hf. rewrite (q05_snez f Hf), q05_known.
  destruct (f =? 0), (4 <=? bv_unsigned c); vm_compute; reflexivity.
Qed.

Definition q05_f (f u : Z) : Z := if (f =? 0) && (4 <=? u) then u else f.

Lemma q05_first_step : forall bs i,
  q05_f (RcPorts.pu_first bs i) (bv_unsigned (nth (8 + i) bs (Z_to_bv 8 0))) = RcPorts.pu_first bs (S i).
Proof.
  intros bs i. cbn [RcPorts.pu_first]. unfold q05_f, RcPorts.rc_u8.
  destruct (b7_first_spec bs i) as ((E1 & E2) & _).
  destruct (Z.eqb_spec (RcPorts.pu_first bs i) 0) as [F0|F0];
    destruct (Z.eqb_spec (RcPorts.pu_nunk bs i) 0) as [N0|N0]; cbn [andb]; try reflexivity; exfalso; tauto.
Qed.

(* 0x13bf0 -> 0x13c3c: one turn of the slot loop on the code c at A3. *)
Lemma q05_body :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A3 x1 x0 x2 f : Z) (c : byte),
    a3 = Z_to_bv 64 A3 -> a1 = Z_to_bv 64 x1 -> a0 = Z_to_bv 64 x0 -> a2 = Z_to_bv 64 x2 -> a6 = Z_to_bv 64 f ->
    0 <= f < 256 ->
    ov_read_bytes rsegs m (Z_to_bv 64 A3) 1 = Some [c] ->
    evt rsegs
      (fun ms' => exists t0' a5' a7' : word,
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1
                       (Z_to_bv 64 (x0 + if RcLeaf.is_out (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x1 + if RcLeaf.is_in (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (x2 + if is_empty (bv_unsigned c) then 1 else 0))
                       (Z_to_bv 64 (A3 + 1)) a4 a5' a5' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c3c) fc None m (seg_rom rsegs) /\
         a5' = Z_to_bv 64 (q05_f f (bv_unsigned c)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13bf0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A3 x1 x0 x2 f c -> -> -> -> -> Hf R.
  step. step. step. step. step. step. step.
  rewrite (q05_br f c Hf).
  destruct ((f =? 0) && (4 <=? bv_unsigned c)) eqn:Ec; cbv iota.
  - step. step. step. step. step. step. step. step. step. step. step.
    rewrite q05_in, q05_out, q05_emp.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. unfold q05_f. rewrite Ec. reflexivity.
  - step. step. step. step. step. step. step. step. step. step. step. step.
    rewrite q05_in, q05_out, q05_emp.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. unfold q05_f. rewrite Ec. reflexivity.
Qed.

(* The loop from turn i (head 0x13bf0) to its exit 0x13c40, for the 20 block bytes bs at Φ + 18. *)
Lemma q05_loop :
  forall (bs : list byte) (phi : Z)
         (ra sp gp tp t1 t2 s0 s1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a4 = Z_to_bv 64 (phi + 38) -> 0 <= phi -> phi + 50 < 2 ^ 64 ->
    (forall k, (k < 12)%nat ->
       ov_read_bytes rsegs m (Z_to_bv 64 (phi + 26 + Z.of_nat k)) 1 = Some [nth (8 + k) bs (Z_to_bv 8 0)]) ->
    forall n i (A3 X0 X1 X2 F6 : Z) (t0 a5 a7 : word), (i + n = 12)%nat -> (0 < n)%nat ->
    A3 = phi + 26 + Z.of_nat i -> X0 = RcLeaf.cnt RcLeaf.is_out bs i -> X1 = RcLeaf.cnt RcLeaf.is_in bs i ->
    X2 = RcLeaf.cnt is_empty bs i -> F6 = RcPorts.pu_first bs i ->
    evt rsegs
      (fun ms' => exists t0' a3' a6' a7' : word,
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (RcLeaf.n_out bs)) (Z_to_bv 64 (RcLeaf.n_in bs))
                       (Z_to_bv 64 (RcLeaf.cnt is_empty bs 12)) a3' a4 (Z_to_bv 64 (RcPorts.pu_first bs 12)) a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c40) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X0) (Z_to_bv 64 X1) (Z_to_bv 64 X2) (Z_to_bv 64 A3) a4 a5
               (Z_to_bv 64 F6) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13bf0) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi ra sp gp tp t1 t2 s0 s1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> Hp0 Hp1 HR.
  induction n as [|n IH]; intros i A3 X0 X1 X2 F6 t0 a5 a7 Hin Hn HA3 HX0 HX1 HX2 HF6; [lia|].
  destruct (b7_first_spec bs i) as (_ & Hf).
  eapply evt_cut.
  { eapply q05_body; [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | |].
    - rewrite HF6. exact Hf.
    - rewrite HA3. exact (HR i ltac:(lia)). }
  intros ms' (t0' & a5' & a7' & -> & Ea5). subst a5' X0 X1 X2 F6.
  rewrite q05_first_step.
  step.
  destruct n as [|n'].
  - b7_br false ltac:(rewrite b7_eqb_small by lia; b7_zdec).
    assert (Ei : i = 11%nat) by lia. subst i.
    apply evt_done. do 4 eexists. reflexivity.
  - b7_br true ltac:(rewrite b7_eqb_small by lia; b7_zdec).
    apply (IH (S i)); [lia | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

(* 0x13bd8 -> 0x13c40 with s6 = blk = Φ + 18 and bs blk's 20 bytes. *)
Lemma q05_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi nin nout nemp pf : Z) (bs : list byte),
    s6 = Z_to_bv 64 (phi + 18) -> 0 <= phi -> phi + 50 < 2 ^ 64 ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    nin = RcLeaf.n_in bs -> nout = RcLeaf.n_out bs -> nemp = RcLeaf.cnt is_empty bs 12 ->
    pf = RcPorts.pu_first bs 12 ->
    evt rsegs
      (fun ms' => exists t0' a3' a4' a6' a7' : word,
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 nout) (Z_to_bv 64 nin)
                       (Z_to_bv 64 nemp) a3' a4' (Z_to_bv 64 pf) a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c40) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13bd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi nin nout nemp pf bs -> Hp0 Hp1 Hl HB -> -> -> ->.
  assert (HR : forall k, (k < 12)%nat ->
            ov_read_bytes rsegs m (Z_to_bv 64 (phi + 26 + Z.of_nat k)) 1 = Some [nth (8 + k) bs (Z_to_bv 8 0)]).
  { intros k Hk. pose proof (b7_rd1 m (phi + 18) bs (8 + k) (Z_to_bv 8 0) HB ltac:(lia)) as E.
    replace (phi + 18 + Z.of_nat (8 + k)) with (phi + 26 + Z.of_nat k) in E by lia. exact E. }
  step. step. step. step. step. step.
  eapply evt_mono.
  { eapply q05_loop with (bs := bs) (phi := phi) (n := 12%nat) (i := 0%nat);
      [first [reflexivity | f_equal; lia] | lia | lia | exact HR | lia | lia | lia | reflexivity | reflexivity |
       reflexivity | reflexivity]. }
  intros ms' (t0' & a3' & a6' & a7' & ->). do 5 eexists. reflexivity.
Qed.

Section Q05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_Q05 : forall j, Hat B APIf ra (Inv_K13c40_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13bd8_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HQB & H24 & Er & Hu)).
  pose proof HQB as (HEQ & H25 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (Hj & H26 & HFC & H21 & Hphi & HOUR & HM7).
  pose proof HVC as (H22 & H24' & HB).
  pose proof (b7_big_8819 _ _ H88) as Hbig.
  destruct (b7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  assert (H22' : rg regs 22 (phi + 18)).
  { unfold t_big in H22. rewrite (proj2 (Z.leb_le _ _) Hbig) in H22. exact H22. }
  destruct (ex_intro (fun u => u = RcLeaf.n_in (t_pbs (g_in g) j)) _ eq_refl) as (NIN & ENIN).
  destruct (ex_intro (fun u => u = RcLeaf.n_out (t_pbs (g_in g) j)) _ eq_refl) as (NOUT & ENOUT).
  destruct (ex_intro (fun u => u = RcLeaf.cnt is_empty (t_pbs (g_in g) j) 12) _ eq_refl) as (NEMP & ENEMP).
  destruct (ex_intro (fun u => u = RcPorts.pu_first (t_pbs (g_in g) j) 12) _ eq_refl) as (PF & EPF).
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply q05_evt with (phi := phi) (bs := t_pbs (g_in g) j) (nin := NIN) (nout := NOUT) (nemp := NEMP) (pf := PF).
    + exact H22'.
    + lia.
    + lia.
    + apply b7_pbs_length.
    + apply b7_pbs_bytes. apply b7_norm; [exact HMI|]. apply b7_g_bytes; [exact Hphi | exact Hbig].
    + exact ENIN.
    + exact ENOUT.
    + exact ENEMP.
    + exact EPF.
  - intros ms (t0' & a3' & a4' & a6' & a7' & ->). do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [apply munch_refl|]. split; [apply wmono_refl|]. intros x _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (t0' & a3' & a4' & a6' & a7' & HE).
    apply b7_MS_inj in HE as (ER & EPC & EM). subst R pc' m0'.
    apply H. unfold Inv_K13c40_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (MT0 : MT [] mem m') by exact (b7_mt [] mem _ m' HMI (munch_refl _ _) Hrel).
    split.
    { apply (b7_QB g j phi regs mem regs' m' []); [exact HQB | exact MT0 | apply b7_DJE_nil | apply b7_DJQ_nil | |].
      - unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    split; [apply (b7_rg regs); [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact H24]|].
    split; [exact Er|]. split; [exact Hu|].
    rewrite <- ENIN, <- ENOUT, <- ENEMP, <- EPF. unfold rg. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

End Q05.
