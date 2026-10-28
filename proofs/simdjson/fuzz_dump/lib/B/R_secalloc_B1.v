(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0 R_mmapfixed R_mapordie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.

Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | clear_big; my_disj ].

Local Ltac disj_try H := let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p.
Module RS.
  Import Ltac2.
  Ltac2 is_hdisj (t : constr) : bool := lazy_match! t with hide (_ \/ _) => true | _ => false end.
  Ltac2 rsearch () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if is_hdisj ty then (if SF2.meets (SF2.vars_of [] ty) gv then Some id else None) else None
                 end) (Control.hyps ()) in
    let rec go l := match l with
      | [] => Control.zero (Tactic_failure None)
      | id :: l' => Control.plus (fun () => ltac1:(h |- disj_try h) (Ltac1.of_constr (Control.hyp id))) (fun _ => go l')
      end in
    go ids.
  Ltac2 rsearch1 () : unit := Control.enter rsearch.
End RS.
Local Ltac disj_rel := ltac2:(RS.rsearch1 ()).
Local Ltac disj_one ::=
  first [ lia_p
        | disj_rel
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].

Definition sb1_W (sp P SZ T PAB n : Z) : list (Z * Z) := ((sp - 464, sp - 96) :: sb_W sp P SZ T PAB n)%Z.

Definition sb1_mid (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (P SZ PAB nres T : Z) (ws : list word) (mm md : word) (m : mem)
    : Prop :=
  exists (jf : list byte) (b : byte) (jj : list byte) (w1 w2 w3 w4 ga gm : word) (bl : list word),
    rw_cells bsegs m (bv_unsigned sp - 96) [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m i_sec_chunks [C8 (Z_to_bv 64 PAB)]
    /\ rw_cells bsegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nres)]
    /\ rw_cells bsegs m i_sec_sorted [C1 b; CB 7 jj; C8 w1; C8 w2; C8 w3; C8 w4]
    /\ length bl = 64%nat /\ u64arr bsegs m i_sec_bylog bl /\ rw_cells bsegs m i_gstat_alloc [C8 ga; C8 gm]
    /\ rw_cells bsegs m i_sec_mutex [C4 (Z_to_bv 64 1)]
    /\ u64arr bsegs m PAB ws /\ sec_range m PAB
    /\ rw_cells bsegs m P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)]
    /\ rw_cells bsegs m (P + 24) [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))]
    /\ rw_cells bsegs m (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)]
    /\ rw_cells bsegs m (shad (P + 4096 + SZ))
         [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))]
    /\ rw_cells bsegs m (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))].

Definition secalloc_B1_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P SZ PAB nres T lo : Z) (ws : list word) (mm md : word) (mA : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (k : Z) (m' : mem),
    ms' = MSsvc (mfi0_regs (Z_to_bv 64 0x5de60) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0' t1' t2' a6'
                   (PAB + 8 * nres) 0x20000 (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ))
                   (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom bsegs)
    /\ munch (sb1_W (bv_unsigned sp) P SZ T PAB nres) mA m' /\ wmono bsegs mA m' /\ mem_inv bsegs m'
    /\ mfi_frame m' (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 0x5de60) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
         (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - k)) (Z_to_bv 64 (P + 4096))
    /\ stk bsegs m' lo (bv_unsigned sp - 192) /\ mm_gcells m'
    /\ (0 <= k < 64)%Z /\ (2 ^ k <= sa_msz SZ < 2 ^ (k + 1))%Z
    /\ sb1_mid sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 P SZ PAB nres T ws mm md m'.

Lemma secalloc_B1_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (mA : mem) (SZ P PAB nres TCX T lo : Z) (ws : list word) (mm md : word) (shj1 shj2 : list byte),
  (65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z ->
  gobj P (sa_msz SZ) lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo -> gobj PAB 0x800000 lo ->
  sapart P (sa_msz SZ) T 4096 -> sapart P (sa_msz SZ) TCX 0xa0 -> sapart T 4096 TCX 0xa0 ->
  sapart P (sa_msz SZ) PAB 0x800000 -> sapart T 4096 PAB 0x800000 ->
  (0 <= nres)%Z -> Z.of_nat (length ws) = nres -> (nres + 16384 <= 2^20)%Z -> (nres mod 16384 = 0)%Z -> (PAB mod 4096 = 0)%Z ->
  sa_frame mA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  mod_frame mA (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
    (Z_to_bv 64 (sa_msz SZ)) ->
  stk bsegs mA lo (bv_unsigned sp - 144) -> mm_gcells mA -> sec_page mA ->
  ps_cells mA -> thread_cells TCX T mA -> rw_cells bsegs mA (T + 2872) [C8 mm; C8 md] ->
  sec_core mA PAB nres nres -> sec_pad mA -> sec_junk mA -> u64arr bsegs mA PAB ws -> sec_range mA PAB ->
  rw_cells bsegs mA (shad P) [CB 512 shj1] ->
  rw_cells bsegs mA (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2] ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs mA ->
  evt bsegs (secalloc_B1_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P SZ PAB nres T lo ws mm md mA)
    (nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6 (sa_msz SZ)
                   (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom bsegs))
          (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])).
Proof.
  intros until shj2. intros HSZ HP GP GT GX GA APT APX ATX APA ATA Hn Hlen Hnres Hnres16 HPAB FR MF ST MM PG PS TH TS SC PAD SJ ARR
    SRG SH1 SH2 HLOH HLO HSP MI.
  eapply (sb_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mA SZ P PAB nres nres TCX T lo ws mm md shj1 shj2);
    [exact HSZ| exact HP| exact GP| exact GT| exact GX| exact GA| exact APT| exact APX| exact ATX| exact APA| exact ATA| lia
    | exact Hlen| lia| exact Hnres16| lia| exact FR| exact MF| exact ST| exact MM| exact PG| exact PS| exact TH| exact TS
    | exact SC| exact PAD| exact SJ| exact ARR| exact SRG| exact SH1| exact SH2| exact HLOH| lia| exact HSP| exact MI|].
  intros m2 ra2 t0' t1' t2' a1' a2' a5' a6' a7' t3' t4' t5' t6' k jf b jj w1 w2 w3 w4 ga gm bl
    MU WM MI2 ST2 FR2 CH NR SJ1 Hbl SJ2 SJ3 LW ARR2 SRG2 MM2 HD3 HI RMP SH1' SH2' TS' Hk Hx.
  clear FR ST MM PG PS TH TS SC PAD SJ ARR SRG SH1 SH2 MI MF.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  pose proof GP as GP0. pose proof GA as GA0. apply box in GP0, GA0.
  destruct GP as (GP1 & GP2 & GP3 & GP4). destruct GT as (GT1 & GT2 & GT3 & GT4). destruct GX as (GX1 & GX2 & GX3 & GX4).
  destruct GA as (GA1 & GA2 & GA3 & GA4).
  clear GX1 GX2 GX3 GX4 APX ATX.
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GP4' : (7131136 <= P)%Z) by (destruct GP4; lia). clear GP4.
  assert (GA4' : (7131136 <= PAB)%Z) by (destruct GA4; lia). clear GA4.
  pose proof (sa_shad_facts P SZ lo HP ltac:(lia) ltac:(lia) (unbox _ GP0) ltac:(lia)) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8 & SRc).
  rewrite SR7 in SH2'. apply box in SR7.
  set (z8 := (SZ / 8)%Z) in *. set (ms8 := (sa_msz SZ / 8)%Z) in *. clearbody z8 ms8.
  assert (MS8 : (8704 <= ms8)%Z) by lia.
  pose proof HSZ as (HSZ1 & HSZ2 & HSZ3).
  apply box in HP, MS2, HSZ2, Hnres16, HSZ, HPAB.
  assert (HL8 : (8 * nres + 0x20000 <= 0x800000)%Z) by lia.
  unfold kHighShadowEnd in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  unfold sec_range, i_sec_range in SRG2. change (INST + 0x50)%Z with 1522472%Z in SRG2.
  change i_sec_chunks with 1522464%Z in CH. change i_sec_nres with 1522504%Z in NR. change i_sec_mutex with 1523072%Z in LW.
  change i_sec_sorted with 1522520%Z in SJ1. change i_sec_bylog with 1522560%Z in SJ2. change i_gstat_alloc with 1523096%Z in SJ3.
  apply (munch_weaken (sb_W (bv_unsigned sp) P SZ T PAB nres) (sb1_W (bv_unsigned sp) P SZ T PAB nres)) in MU;
    [| intros x Hxo; cbn [sb1_W outside] in Hxo; clear - Hxo; tauto].
  unfold sb1_W, sb_W in MU.
  change i_sec_nres with 1522504%Z in MU. change i_sec_sorted with 1522520%Z in MU. change i_sec_bylog with 1522560%Z in MU.
  change i_gstat_alloc with 1523096%Z in MU. change i_sec_mutex with 1523072%Z in MU.
  pose proof MM2 as (G1 & G2 & G3 & G4 & G5). clear MM2.
  unfold kHighShadowEnd in *.
  change SEC with 1522456%Z. change GSTAT with 1523080%Z.
  hide_disj.
  zstep. ifT.
  do 8 zstep.
  replace (nres ≪ 3 + PAB)%Z with (PAB + 8 * nres)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep.
  call (mapordie_A_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (PAB + 8 * nres) 0x20000 lo).
  all: rewrite ?ESP.
  1:{ lia. }
  1:{ pose proof (unbox _ HPAB). pose proof (unbox _ Hnres16). Z.div_mod_to_equations. lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ lia. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  1:{ exact ST2. }
  1:{ unfold kHighShadowEnd. lia. }
  1:{ lia. }
  1:{ lia. }
  1:{ assumption. }
  apply evt_done. unfold secalloc_B1_post. do 8 eexists. exists k. eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  split; [rewrite ESP in *; replace (bv_unsigned sp - 192)%Z with (bv_unsigned sp - 96 - 96)%Z by lia; assumption|].
  split; [assumption|]. split; [exact Hk|]. split; [exact Hx|].
  unfold sb1_mid. exists jf, b, jj, w1, w2, w3, w4, ga, gm, bl.
  split; [exact FR2|]. split; [exact CH|]. split; [exact NR|]. split; [exact SJ1|]. split; [exact Hbl|]. split; [exact SJ2|].
  split; [exact SJ3|]. split; [exact LW|]. split; [exact ARR2|]. split; [unfold sec_range, i_sec_range; exact SRG2|].
  split; [exact HD3|]. split; [exact HI|]. split; [exact RMP|]. split; [exact SH1'|].
  split; [rewrite (unbox _ SR7); exact SH2'| exact TS'].
Qed.
