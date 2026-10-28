(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0.
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

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.

Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | unfold hide in *; sf_unhide; dj_prune; Zify.zify; xlia zchecker
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | clear_big; my_disj ].

Lemma secalloc_B_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (mA : mem) (SZ P PAB nres n TCX T lo : Z) (ws : list word) (mm md : word) (shj1 shj2 : list byte),
  (65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z ->
  gobj P (sa_msz SZ) lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo -> gobj PAB 0x800000 lo ->
  sapart P (sa_msz SZ) T 4096 -> sapart P (sa_msz SZ) TCX 0xa0 -> sapart T 4096 TCX 0xa0 ->
  sapart P (sa_msz SZ) PAB 0x800000 -> sapart T 4096 PAB 0x800000 ->
  (0 <= n < nres)%Z -> Z.of_nat (length ws) = nres -> (nres <= 2^20)%Z -> (nres mod 16384 = 0)%Z ->
  sa_frame mA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  mod_frame mA (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
    (Z_to_bv 64 (sa_msz SZ)) ->
  stk bsegs mA lo (bv_unsigned sp - 144) -> mm_gcells mA -> sec_page mA ->
  ps_cells mA -> thread_cells TCX T mA -> rw_cells bsegs mA (T + 2872) [C8 mm; C8 md] ->
  sec_core mA PAB nres n -> sec_pad mA -> sec_junk mA -> u64arr bsegs mA PAB ws -> sec_range mA PAB ->
  rw_cells bsegs mA (shad P) [CB 512 shj1] ->
  rw_cells bsegs mA (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2] ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs mA ->
  evt bsegs (secalloc_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (sb_W (bv_unsigned sp) P SZ T PAB n) (P + 4096) lo mA (sb_K P SZ PAB nres n T ws mm md))
    (nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6 (sa_msz SZ)
                   (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom bsegs))
          (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])).
Proof.
  intros until shj2. intros HSZ HP GP GT GX GA APT APX ATX APA ATA Hn Hlen Hnres Hnres16 FR MF ST MM PG PS TH TS SC PAD SJ ARR
    SRG SH1 SH2 HLOH HLO HSP MI.
  eapply (sb_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mA SZ P PAB nres n TCX T lo ws mm md shj1 shj2);
    [exact HSZ| exact HP| exact GP| exact GT| exact GX| exact GA| exact APT| exact APX| exact ATX| exact APA| exact ATA| lia
    | exact Hlen| exact Hnres| exact Hnres16| lia| exact FR| exact MF| exact ST| exact MM| exact PG| exact PS| exact TH| exact TS
    | exact SC| exact PAD| exact SJ| exact ARR| exact SRG| exact SH1| exact SH2| exact HLOH| exact HLO| exact HSP| exact MI|].
  intros m2 ra2 t0' t1' t2' a1' a2' a5' a6' a7' t3' t4' t5' t6' k jf b jj w1 w2 w3 w4 ga gm bl
    MU WM MI2 ST2 FR2 CH NR SJ1 Hbl SJ2 SJ3 LW ARR2 SRG2 MM2 HD3 HI RMP SH1' SH2' TS' Hk Hx.
  clear FR ST MM PG PS TH TS SC PAD SJ ARR SRG SH1 SH2 MI SRG2 MM2 MF.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  pose proof GP as GP0. pose proof GA as GA0. pose proof APA as APA0. apply box in GP0, GA0, APA0.
  destruct GP as (GP1 & GP2 & GP3 & GP4). destruct GT as (GT1 & GT2 & GT3 & GT4). destruct GX as (GX1 & GX2 & GX3 & GX4).
  destruct GA as (GA1 & GA2 & GA3 & GA4).
  clear GX1 GX2 GX3 GX4 APX ATX.
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GP4' : (7135232 <= P)%Z) by (destruct GP4; lia). clear GP4.
  assert (GA4' : (7135232 <= PAB)%Z) by (destruct GA4; lia). clear GA4.
  pose proof (sa_shad_facts P SZ lo HP ltac:(lia) ltac:(lia) (unbox _ GP0) ltac:(lia)) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8 & SRc).
  rewrite SR7 in SH2'. apply box in SR7.
  set (z8 := (SZ / 8)%Z) in *. set (ms8 := (sa_msz SZ / 8)%Z) in *. clearbody z8 ms8.
  assert (MS8 : (8704 <= ms8)%Z) by lia.
  pose proof HSZ as (HSZ1 & HSZ2 & HSZ3).
  apply box in HP, MS2, HSZ2, Hnres16, HSZ.
  assert (HL8 : (8 * nres <= 0x800000)%Z) by lia.
  change i_sec_chunks with 1525152%Z in CH. change i_sec_nres with 1525192%Z in NR. change i_sec_mutex with 1525760%Z in LW.
  change i_sec_sorted with 1525208%Z in SJ1. change i_sec_bylog with 1525248%Z in SJ2. change i_gstat_alloc with 1525784%Z in SJ3.
  unfold sb_W in MU.
  change i_sec_nres with 1525192%Z in MU. change i_sec_sorted with 1525208%Z in MU. change i_sec_bylog with 1525248%Z in MU.
  change i_gstat_alloc with 1525784%Z in MU. change i_sec_mutex with 1525760%Z in MU.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  hide_disj.
  zhide.
  zstep.
  ifF.
  eapply evt_mono.
  1:{ eapply (sa_p4 ra2 t0' t1' t2' a1' a2' (Z_to_bv 64 nres) a5' a6' a7' (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ))
        (Z_to_bv 64 (P + 4096 + SZ)) t3' t4' t5' t6' (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) s10 s11 F fc
        ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jf m2 P SZ PAB nres n k lo ws).
      1:{ lia. }
      1:{ exact (unbox _ HP). }
      1:{ exact Hk. }
      1:{ exact (unbox _ GP0). }
      1:{ destruct (unbox _ GA0) as (? & ? & ? & ?). split; [lia|]. split; [lia|]. split; lia. }
      1:{ destruct (unbox _ APA0); [left; lia| right; lia]. }
      1:{ lia. }
      1:{ rewrite ESP. exact FR2. }
      1:{ rewrite ESP. exact ST2. }
      1:{ unfold kHighShadowEnd. lia. }
      1:{ rewrite ESP. lia. }
      1:{ rewrite ESP. lia. }
      1:{ exact CH. }
      1:{ exact NR. }
      1:{ unfold sec_junk. split; [do 6 eexists; exact SJ1|]. split; [eexists; split; [exact Hbl| exact SJ2]|].
          do 2 eexists; exact SJ3. }
      1:{ exact LW. }
      1:{ exact ARR2. }
      1:{ exact HI. }
      1:{ assumption. } }
  intros ms' PO.
  rewrite ESP in PO. replace (bv_unsigned sp - 96 + 96)%Z with (bv_unsigned sp) in PO by lia. rewrite Z_to_bv_bv_unsigned in PO.
  unfold secalloc_post in PO.
  destruct PO as (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m3 & E & MU4 & WM4 & MI4 & ST4
                  & (HI' & ARR' & NR' & SJ' & MX' & PAD')).
  subst ms'.
  clear FR2 ST2 NR SJ1 SJ2 SJ3 LW ARR2 HI.
  unfold sa_W4 in MU4.
  change i_sec_nres with 1525192%Z in MU4. change i_sec_sorted with 1525208%Z in MU4. change i_sec_bylog with 1525248%Z in MU4.
  change i_gstat_alloc with 1525784%Z in MU4. change i_sec_mutex with 1525760%Z in MU4.
  transport_after_call bsegs m2 m3 MU4 WM4. clear MU4 WM4.
  unfold secalloc_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact ST4|].
  unfold sb_K. split.
  - unfold shdr.
    apply (sec_rw_app2 _ P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] [C8 (Z_to_bv 64 n)]).
    split; [exact HD3| exact HI'].
  - split; [exact RMP|]. split; [exact SH1'|]. split; [rewrite (unbox _ SR7); exact SH2'|]. split; [exact TS'|].
    split; [split; [exact CH| split; [exact NR'| exact MX']]|]. split; [exact PAD'|]. split; [exact SJ'| exact ARR'].
Qed.
