(* WireCmPre: cm_pre_stmt of lib/B/Prog/WireCmIface.v, the inlined test of check_meter (fuzz_wire.asan-ubsan,
   0x8026c .. 0x80328) as a footprint run in continuation form. cm_tail runs 0x802c0 .. 0x80328 (the n >= 1000 test of
   f[eo], f[eo + 1]); cm_pre runs 0x8026c .. 0x802c0 (n < 14 to 0x80318; else the f[12], f[13] tests that set
   s9 := 12 / 16) and hands over to cm_tail. Each byte load is behind its shadow check (lib/B/AsanCells.v
   addressable, the k = 0 / k <> 0 cases), each UBSan wrap check falls through (f + 20 < 2^64). Proof idioms from
   reac-repacer/fuzz_uci lib/B/Prog/UciCvBSegs.v (recipes commit 0295462466b2) and lib/B/Prog/AsanKAProof.v. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr WireCmIface.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Lemma cm_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
  intros a n Hn Ha.
  assert (Hlog : Z.log2 a < n).
  { destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|]. apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
  rewrite <- (Z.ldiff_ones_l_low a n) by lia.
  rewrite Z.ldiff_land.
  assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
  rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
  replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma cm_not_u : forall x : word,
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned x) 18446744073709551615)) = 2 ^ 64 - 1 - bv_unsigned x.
Proof.
  intros x. pose proof (zr_word x) as Rx. unfold inr64 in Rx.
  change 18446744073709551615 with (Z.ones 64). rewrite cm_lxor_ones by lia.
  change (Z.ones 64) with (2 ^ 64 - 1). apply unsigned_lit. lia.
Qed.

Lemma cm_zxb_eqb : forall (b : byte) z, 0 <= z < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 z) = (bv_unsigned b =? z).
Proof.
  intros b z Hz. pose proof (byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma cm_seqz25 : forall b : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -25)) 1 = Z_to_bv 64 (if bv_unsigned b =? 25 then 1 else 0).
Proof.
  intros b. pose proof (byte_range b). unfold v_sltiu, zxb.
  rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (bv_unsigned b) 25) as [E|N].
  - rewrite E. reflexivity.
  - destruct (Z.ltb_spec ((bv_unsigned b + -25) mod 2 ^ 64) 1); [|reflexivity].
    exfalso. Z.div_mod_to_equations. lia.
Qed.

Ltac cm_lit X := let v := eval vm_compute in X in change X with v.
Ltac cm_lits :=
  repeat match goal with
  | |- context [CM_CTR] => cm_lit CM_CTR
  | |- context [CM_PRE] => cm_lit CM_PRE
  | |- context [CM_AT ?o] => cm_lit (CM_AT o)
  | |- context [CM_ENTRY] => cm_lit CM_ENTRY
  end.
(* the image-B entry of 0x802c0 (+0x154), where cm_tail starts *)
Ltac cm_at_tail :=
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
    change (Z_to_bv 64 p) with (Z_to_bv 64 (CM_AT 0x154)) end.
(* the continuation applied to the four argument registers the path leaves *)
Ltac cm_k K :=
  let v10 := reg_val 10 in let v11 := reg_val 11 in let v12 := reg_val 12 in let v13 := reg_val 13 in
  exact (K v10 v11 v12 v13).
(* one shadow check: k = 0 falls through `bnez`; k <> 0 takes it, and `andi` / `blt` return (the address mod 8 < k) *)
Ltac cm_shadow SK k MB U :=
  let C := fresh "C" in let Cu := fresh "Cu" in
  destruct SK as [C|[C Cu]];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7, U, (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

Lemma cm_tail :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s10 s11 t3 t4 t5 t6 fw : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n e : Z) (bs : list byte)
         (Q : machine_state -> Prop),
    14 <= n < 2 ^ 64 -> 4096 <= bv_unsigned fw -> bv_unsigned fw + 20 < 2 ^ 64 ->
    Z.of_nat (PMC.meter_eo n bs) = e -> 12 <= e <= 16 ->
    (1000 <= n -> forall i, 12 <= i < 20 -> mrd rsegs m (wa (bv_unsigned fw + i)) = Some (cm_byte bs i)) ->
    (1000 <= n -> addressable m (bv_unsigned fw + 12) 8) ->
    (1000 <= n -> ExecF.rng RNG (bv_unsigned fw + 12) 8) ->
    (1000 <= n -> ExecF.rng RNG (shadow_addr (bv_unsigned fw + 12))
                    (shadow_addr (bv_unsigned fw + 19) - shadow_addr (bv_unsigned fw + 12) + 1)) ->
    (forall a0' a1' a2' a3' : word,
       ExecF.evtF rsegs RNG Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 fw (Z_to_bv 64 n) s5 s6 s7
                  (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs))) (Z_to_bv 64 (cm_bit n bs))
                  s11 t3 t4 t5 t6)
             F (Z_to_bv 64 CM_CTR) fc None m (seg_rom rsegs))) ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 fw (Z_to_bv 64 n)
               s5 s6 s7 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 e) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (CM_AT 0x154)) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s10 s11 t3 t4 t5 t6 fw F fc m n e bs Q
    HN F0 F1 EO HE RD8 AD8 RB8 RS8 K.
  cm_lits.
  let v := eval vm_compute in CM_CTR in change CM_CTR with v in K.
  rewrite EO in K.
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ue : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  pose proof (zr_word fw) as Rf. unfold inr64 in Rf.
  destruct (Z.ltb_spec n 1000) as [LT|GE].
  - (* n < 1000: `li a0, 1000`, `bltu s4, a0` taken to +0x1b8: s10 := 0 *)
    assert (CB : cm_bit n bs = 0).
    { unfold cm_bit, PMC.meter_ok. cbv zeta. rewrite (proj2 (Z.leb_gt 1000 n) LT), andb_false_r. reflexivity. }
    rewrite CB in K.
    step. step. if_true. step.
    cm_k K.
  - (* n >= 1000 *)
    assert (CBV : cm_bit n bs =
                  if (bv_unsigned (cm_byte bs e) =? 136) && (bv_unsigned (cm_byte bs (e + 1)) =? 25) then 1 else 0).
    { unfold cm_bit, PMC.meter_ok, PMC.meter_byte, cm_byte. cbv zeta.
      rewrite <- EO, Nat2Z.id.
      replace (Z.to_nat (Z.of_nat (PMC.meter_eo n bs) + 1)) with (PMC.meter_eo n bs + 1)%nat by lia.
      rewrite (proj2 (Z.leb_le (Z.of_nat (PMC.meter_eo n bs) + 6) n)) by lia.
      rewrite (proj2 (Z.leb_le 1000 n)) by lia. reflexivity. }
    rewrite CBV in K. clear CBV.
    destruct (AD8 GE) as (P0 & N0 & PE & AB).
    pose proof (RD8 GE) as RD. specialize (RB8 GE). specialize (RS8 GE). clear RD8 AD8.
    destruct (AB (e - 12) ltac:(lia)) as (APa & ka & MKa & SKa).
    destruct (AB (e - 11) ltac:(lia)) as (APb & kb & MKb & SKb).
    clear AB.
    pose proof (RD e ltac:(lia)) as Fa. pose proof (RD (e + 1) ltac:(lia)) as Fb. clear RD.
    unfold shadow_addr, ASAN_K, shadow_ok in *.
    replace (bv_unsigned fw + 12 + (e - 12)) with (bv_unsigned fw + e) in MKa, SKa by lia.
    replace (bv_unsigned fw + 12 + (e - 11)) with (bv_unsigned fw + e + 1) in MKb, SKb by lia.
    replace (bv_unsigned fw + (e + 1)) with (bv_unsigned fw + e + 1) in Fb by lia.
    assert (DV1 : (bv_unsigned fw + 12) / 8 <= (bv_unsigned fw + e) / 8) by (apply Z.div_le_mono; lia).
    assert (DV2 : (bv_unsigned fw + e) / 8 <= (bv_unsigned fw + e + 1) / 8) by (apply Z.div_le_mono; lia).
    assert (DV3 : (bv_unsigned fw + e + 1) / 8 <= (bv_unsigned fw + 19) / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.mod_pos_bound (bv_unsigned fw + e) 8 ltac:(lia)) as MBa.
    pose proof (Z.mod_pos_bound (bv_unsigned fw + e + 1) 8 ltac:(lia)) as MBb.
    set (ba := cm_byte bs e) in *. set (bb := cm_byte bs (e + 1)) in *. clearbody ba bb.
    (* `li a0, 1000`, `bltu s4, a0` not taken *)
    step. step. if_false.
    (* `not a1, s3`; `bltu a1, s9` (UBSan: f + eo wraps) not taken *)
    step.
    remember (Z_to_bv 64 (Z.lxor (bv_unsigned fw) 18446744073709551615)) as nf eqn:Enf.
    assert (Unf : bv_unsigned nf = 2 ^ 64 - 1 - bv_unsigned fw) by (rewrite Enf; apply cm_not_u).
    clear Enf.
    step. if_false.
    (* f + eo: `add a0, s3, s9`, its shadow byte and check *)
    step. gen_addi fw wA Ua.
    step. gen_shr wA gA Ga. rewrite Ua in Ga.
    step. gen_addi gA hA Ha.
    pose proof (rdw0 m hA _ _ MKa ltac:(lia)) as R. step. clear R.
    step.
    cm_shadow SKa ka MBa Ua.
    (* f[eo] (`lbu`), `li a3, 0x88`, `bne a2, a3` *)
    all: pose proof (rdw0 m wA _ _ Fa ltac:(lia)) as R; step; clear R.
    all: step; step.
    (* destruct rewrites the test in K too *)
    all: rewrite cm_zxb_eqb by lia.
    all: destruct (Z.eqb_spec (bv_unsigned ba) 136) as [E88|N88]; cbn [negb].
    all: lazymatch goal with
         | N88 : bv_unsigned _ <> 136 |- _ => step; cm_k K   (* +0x1b8: s10 := 0 *)
         | _ => idtac
         end.
    (* `bgeu s9, a1` (UBSan: f + eo + 1 wraps) not taken; `addi a0, a0, 1`, its shadow byte and check *)
    all: step; if_false.
    all: step; gen_addi wA wB Ub.
    all: rewrite Ua in Ub.
    all: step; gen_shr wB gB Gb.
    all: rewrite Ub in Gb.
    all: step; gen_addi gB hB Hb.
    all: pose proof (rdw0 m hB _ _ MKb ltac:(lia)) as R; step; clear R.
    all: step.
    all: cm_shadow SKb kb MBb Ub.
    (* f[eo + 1] (`lbu`), `addi a0, a0, -25`, `seqz s10, a0`, `j` +0x1bc *)
    all: pose proof (rdw0 m wB _ _ Fb ltac:(lia)) as R; step; clear R.
    all: step; step; step.
    all: rewrite cm_seqz25.
    all: cm_k K.
Qed.

(* meter_eo from the two tests of f[12], f[13] the path took *)
Ltac cm_eo bs Eba Ebb :=
  unfold PMC.meter_eo, PMC.meter_byte;
  change (nth 12 bs (Z_to_bv 8 0)) with (cm_byte bs 12); change (nth 13 bs (Z_to_bv 8 0)) with (cm_byte bs 13);
  rewrite <- Eba, <- Ebb; rewrite (proj2 (Z.ltb_lt 13 _)) by lia;
  repeat match goal with
  | H : bv_unsigned ?b = ?c |- context [bv_unsigned ?b =? ?c] => rewrite (proj2 (Z.eqb_eq _ _) H)
  | H : bv_unsigned ?b <> ?c |- context [bv_unsigned ?b =? ?c] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end; reflexivity.

Ltac cm_go ev EOc RD8 AD8 RB8 RS8 K :=
  cm_at_tail; eapply cm_tail with (e := ev);
  [ lia | lia | lia | exact EOc | lia | exact RD8 | exact AD8 | exact RB8 | exact RS8 | exact K ].

Lemma cm_pre : cm_pre_stmt.
Proof.
  unfold cm_pre_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m f n bs Q
    HN HL FR RD2 RD8 AD2 AD8 RB2 RS2 RB8 RS8 K.
  cm_lits.
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (Z.ltb_spec n 14) as [LT|GE].
  - (* n < 14: `bltu s4, a0` taken to +0x1ac: s10 := 0, s9 := 12, `j` +0x1bc *)
    assert (EO : PMC.meter_eo n bs = 12%nat).
    { unfold PMC.meter_eo. rewrite (proj2 (Z.ltb_ge 13 n) ltac:(lia)). reflexivity. }
    assert (CB : cm_bit n bs = 0).
    { unfold cm_bit, PMC.meter_ok. cbv zeta. rewrite (proj2 (Z.leb_gt 1000 n) ltac:(lia)), andb_false_r.
      reflexivity. }
    rewrite EO, CB in K.
    let v := eval vm_compute in CM_CTR in change CM_CTR with v in K.
    step. if_true. step. step. step.
    cm_k K.
  - (* n >= 14 *)
    destruct (FR GE) as [F0 F1]. clear FR.
    assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
    remember (Z_to_bv 64 f) as fw eqn:Efw. clear Efw. subst f.
    destruct (AD2 GE) as (P0 & N0 & PE & AB).
    pose proof (RD2 GE) as RD. clear AD2 RD2.
    destruct (AB 0 ltac:(lia)) as (APa & ka & MKa & SKa).
    destruct (AB 1 ltac:(lia)) as (APb & kb & MKb & SKb).
    clear AB.
    pose proof (RD 12 ltac:(lia)) as Fa. pose proof (RD 13 ltac:(lia)) as Fb. clear RD.
    unfold shadow_addr, ASAN_K, shadow_ok in MKa, SKa, MKb, SKb.
    rewrite Z.add_0_r in MKa, SKa.
    replace (bv_unsigned fw + 12 + 1) with (bv_unsigned fw + 13) in MKb, SKb by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned fw + 12) 8 ltac:(lia)) as MBa.
    pose proof (Z.mod_pos_bound (bv_unsigned fw + 13) 8 ltac:(lia)) as MBb.
    remember (cm_byte bs 12) as ba eqn:Eba. remember (cm_byte bs 13) as bb eqn:Ebb.
    specialize (RB2 GE). specialize (RS2 GE).
    unfold shadow_addr, ASAN_K in RS2 |- *.
    assert (DV : (bv_unsigned fw + 12) / 8 <= (bv_unsigned fw + 13) / 8) by (apply Z.div_le_mono; lia).
    (* `bltu s4, a0` (a0 = 14) not taken; `li a0, -12`, `bgeu s3, a0` (UBSan: f + 12 wraps) not taken *)
    step. if_false. step. step. if_false.
    (* f + 12: `addi a0, s3, 12`, its shadow byte and check *)
    step. gen_addi fw wA Ua.
    step. gen_shr wA gA Ga. rewrite Ua in Ga.
    step. gen_addi gA hA Ha.
    pose proof (rdw0 m hA _ _ MKa ltac:(lia)) as R. step. clear R.
    step.
    cm_shadow SKa ka MBa Ua.
    (* f[12] (`lbu`), `li a1, 0x81`, `bne a0, a1` *)
    all: pose proof (rdw0 m wA _ _ Fa ltac:(lia)) as R; step; clear R.
    all: step; step.
    all: rewrite cm_zxb_eqb by lia.
    all: destruct (Z.eqb_spec (bv_unsigned ba) 129) as [E81|N81]; cbn [negb].
    (* f[12] <> 0x81: +0x150 `li s9, 12` *)
    all: lazymatch goal with
         | N81 : bv_unsigned _ <> 129 |- _ =>
             step; assert (EOc : Z.of_nat (PMC.meter_eo n bs) = 12) by cm_eo bs Eba Ebb;
             cm_go 12 EOc RD8 AD8 RB8 RS8 K
         | _ => idtac
         end.
    (* `li a0, -14`, `bltu a0, s3` (UBSan: f + 13 wraps) not taken *)
    all: step; step; if_false.
    (* f + 13: `addi a0, s3, 13`, its shadow byte and check *)
    all: step; gen_addi fw wB Ub.
    all: step; gen_shr wB gB Gb.
    all: rewrite Ub in Gb.
    all: step; gen_addi gB hB Hb.
    all: pose proof (rdw0 m hB _ _ MKb ltac:(lia)) as R; step; clear R.
    all: step.
    all: cm_shadow SKb kb MBb Ub.
    (* f[13] (`lbu`), `beqz a0` *)
    all: pose proof (rdw0 m wB _ _ Fb ltac:(lia)) as R; step; clear R.
    all: step.
    all: rewrite cm_zxb_eqb by lia.
    all: destruct (Z.eqb_spec (bv_unsigned bb) 0) as [E00|N00]; cbn [negb].
    (* f[13] = 0: +0x2fc `li s9, 16`, `j` +0x154; else +0x150 `li s9, 12` *)
    all: lazymatch goal with
         | N00 : bv_unsigned _ <> 0 |- _ =>
             step; assert (EOc : Z.of_nat (PMC.meter_eo n bs) = 12) by cm_eo bs Eba Ebb;
             cm_go 12 EOc RD8 AD8 RB8 RS8 K
         | _ =>
             step; step; assert (EOc : Z.of_nat (PMC.meter_eo n bs) = 16) by cm_eo bs Eba Ebb;
             cm_go 16 EOc RD8 AD8 RB8 RS8 K
         end.
Qed.
