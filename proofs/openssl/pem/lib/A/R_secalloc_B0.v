(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | clear_big; my_disj ].
(* [comment removed for export] *)
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

Lemma zero_split32 : forall (m : mem) A N, (32 <= N)%Z ->
  rw_cells asegs m A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
  rw_cells asegs m A [CB 32 (repeat (Z_to_bv 8 0) 32)]
  /\ rw_cells asegs m (A + 32) [CB (Z.to_nat (N - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (N - 32)))].
Proof.
  intros m A N HN H.
  assert (E : Z.to_nat N = (32 + Z.to_nat (N - 32))%nat) by lia.
  rewrite E, repeat_app in H.
  apply (sec_rw_app2 m A [CB 32 (repeat (Z_to_bv 8 0) 32)] [CB (Z.to_nat (N - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (N - 32)))]).
  eapply sec_relist; [exact H| | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity].
  cbn [cells_wf cell_wf app]. rewrite !repeat_length. repeat split; reflexivity || exact I.
Qed.

(* [comment removed for export] *)
Definition sb_W (sp P SZ T PAB n : Z) : list (Z * Z) :=
  [(P, P + sa_msz SZ); (sp - 160, sp - 96); (shad P, shad P + 512); (shad (P + 4096 + SZ), shad (P + sa_msz SZ));
   (T + 2872, T + 2888); (i_sec_mutex, i_sec_mutex + 4); (PAB + 8 * n, PAB + 8 * n + 8); (i_sec_nres + 8, i_sec_nres + 16);
   (i_sec_sorted, i_sec_sorted + 40); (i_sec_bylog, i_sec_bylog + 512); (i_gstat_alloc, i_gstat_alloc + 16)]%Z.

(* [comment removed for export] *)
Definition sb_K (P SZ PAB nres n T : Z) (ws : list word) (mm md : word) (m : mem) : Prop :=
  shdr m P (sa_msz SZ) SZ n
  /\ rw_cells asegs m (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))]
  /\ rw_cells asegs m (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)]
  /\ rw_cells asegs m (shad (P + 4096 + SZ))
       [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))]
  /\ rw_cells asegs m (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))]
  /\ sec_core m PAB nres (n + 1) /\ sec_pad m /\ sec_junk m /\ u64arr asegs m PAB (upd ws (Z.to_nat n) (Z_to_bv 64 P)).

Lemma sb_common : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (mA : mem) (SZ P PAB nres n TCX T lo : Z) (ws : list word) (mm md : word) (shj1 shj2 : list byte)
    (Q : machine_state -> Prop),
  (65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z ->
  gobj P (sa_msz SZ) lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo -> gobj PAB 0x800000 lo ->
  sapart P (sa_msz SZ) T 4096 -> sapart P (sa_msz SZ) TCX 0xa0 -> sapart T 4096 TCX 0xa0 ->
  sapart P (sa_msz SZ) PAB 0x800000 -> sapart T 4096 PAB 0x800000 ->
  (0 <= n <= nres)%Z -> Z.of_nat (length ws) = nres -> (nres <= 2^20)%Z -> (nres mod 16384 = 0)%Z -> (n < 2^20)%Z ->
  sa_frame mA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  mod_frame mA (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
    (Z_to_bv 64 (sa_msz SZ)) ->
  stk asegs mA lo (bv_unsigned sp - 144) -> mm_gcells mA -> sec_page mA ->
  ps_cells mA -> thread_cells TCX T mA -> rw_cells asegs mA (T + 2872) [C8 mm; C8 md] ->
  sec_core mA PAB nres n -> sec_pad mA -> sec_junk mA -> u64arr asegs mA PAB ws -> sec_range mA PAB ->
  rw_cells asegs mA (shad P) [CB 512 shj1] ->
  rw_cells asegs mA (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2] ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs mA ->
  (forall (m2 : mem) (ra2 t0' t1' t2' a1' a2' a5' a6' a7' t3' t4' t5' t6' : word) (k : Z) (jf : list byte) (b : byte)
      (jj : list byte) (w1 w2 w3 w4 ga gm : word) (bl : list word),
    munch (sb_W (bv_unsigned sp) P SZ T PAB n) mA m2 -> wmono asegs mA m2 -> mem_inv asegs m2 ->
    stk asegs m2 lo (bv_unsigned sp - 96) ->
    rw_cells asegs m2 (bv_unsigned sp - 96) [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 i_sec_chunks [C8 (Z_to_bv 64 PAB)] ->
    rw_cells asegs m2 i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 n)] ->
    rw_cells asegs m2 i_sec_sorted [C1 b; CB 7 jj; C8 w1; C8 w2; C8 w3; C8 w4] ->
    length bl = 64%nat -> u64arr asegs m2 i_sec_bylog bl -> rw_cells asegs m2 i_gstat_alloc [C8 ga; C8 gm] ->
    rw_cells asegs m2 i_sec_mutex [C4 (Z_to_bv 64 1)] ->
    u64arr asegs m2 PAB ws -> sec_range m2 PAB -> mm_gcells m2 ->
    rw_cells asegs m2 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] ->
    rw_cells asegs m2 (P + 24) [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m2 (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))] ->
    rw_cells asegs m2 (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)] ->
    rw_cells asegs m2 (shad (P + 4096 + SZ))
      [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))] ->
    rw_cells asegs m2 (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))] ->
    (0 <= k < 64)%Z -> (2 ^ k <= sa_msz SZ < 2 ^ (k + 1))%Z ->
    evt asegs Q
      (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
               (Z_to_bv 64 (P + 4096)) a1' a2' (Z_to_bv 64 n) (Z_to_bv 64 nres) a5' a6' a7' (Z_to_bv 64 (sa_msz SZ))
               (Z_to_bv 64 (63 - k)) (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ))
               (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x19fa04) fc None m2 (seg_rom asegs))) ->
  evt asegs Q
    (nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6 (sa_msz SZ)
                   (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom asegs))
          (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])).
Proof.
  intros until Q. intros HSZ HP GP GT GX GA APT APX ATX APA ATA Hn Hlen Hnres Hnres16 Hn20 FR MF ST MM PG PS TH TS SC PAD SJ ARR
    SRG SH1 SH2 HLOH HLO HSP MI K0.
  pose proof (sa_msz_facts SZ ltac:(lia)) as [MS1 MS2].
  pose proof HSZ as (HSZ1 & HSZ2 & HSZ3).
  pose proof GP as GP0. pose proof GT as GT0. pose proof GX as GX0. pose proof GA as GA0.
  pose proof APT as APT0. pose proof APX as APX0. pose proof ATX as ATX0. pose proof APA as APA0. pose proof ATA as ATA0.
  apply box in GP0, GT0, GX0, GA0, APT0, APX0, ATX0, APA0, ATA0.
  destruct GP as (GP1 & GP2 & GP3 & GP4). destruct GT as (GT1 & GT2 & GT3 & GT4). destruct GX as (GX1 & GX2 & GX3 & GX4).
  destruct GA as (GA1 & GA2 & GA3 & GA4).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  (* [comment removed for export] *)
  assert (GP4' : (12345344 <= P)%Z) by (destruct GP4; lia). clear GP4.
  assert (GA4' : (12345344 <= PAB)%Z) by (destruct GA4; lia).
  clear GA4.
  pose proof (sa_shad_facts P SZ lo HP ltac:(lia) ltac:(lia) (unbox _ GP0) ltac:(lia)) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8 & SRc).
  rewrite SR7 in SH2. apply box in SR7.
  set (z8 := (SZ / 8)%Z) in *. set (ms8 := (sa_msz SZ / 8)%Z) in *. clearbody z8 ms8.
  assert (MS8 : (8704 <= ms8)%Z) by lia.
  assert (HL8 : (8 * nres <= 0x800000)%Z) by lia.
  apply box in HP, MS2, HSZ2, Hnres16, HSZ.
  (* [comment removed for export] *)
  unfold sec_page, i_sec_page in PG. change (INST + 0x40)%Z with 6722840%Z in PG.
  ps_cells_destr PS.
  destruct TH as ((KI & KK & TSD & T0) & TT).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, tpA in KI, KK, TSD, T0.
  destruct SC as (CH & NR & MX). change i_sec_chunks with 6722848%Z in CH. change i_sec_nres with 6722888%Z in NR.
  change i_sec_mutex with 6723456%Z in MX.
  unfold sec_pad in PAD. change (i_sec_mutex + 1)%Z with 6723457%Z in PAD.
  destruct SJ as ((b & jj & w1 & w2 & w3 & w4 & SJ1) & (bl & Hbl & SJ2) & (ga & gm & SJ3)).
  change i_sec_sorted with 6722904%Z in SJ1. change i_sec_bylog with 6722944%Z in SJ2. change i_gstat_alloc with 6723480%Z in SJ3.
  pose proof MM as (G1 & G2 & G3 & G4 & G5). clear MM.
  unfold sec_range, i_sec_range in SRG. change (INST + 0x50)%Z with 6722856%Z in SRG.
  destruct FR as (jf & FR).
  pose proof (munch_refl (sb_W (bv_unsigned sp) P SZ T PAB n) mA) as MU. unfold sb_W in MU.
  change i_sec_nres with 6722888%Z in MU. change i_sec_sorted with 6722904%Z in MU. change i_sec_bylog with 6722944%Z in MU.
  change i_gstat_alloc with 6723480%Z in MU. change i_sec_mutex with 6723456%Z in MU.
  pose proof (wmono_refl asegs mA) as WM.
  pose proof (roundup4k_id (sa_msz SZ) (unbox _ MS2)) as RU.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  hide_disj.
  eapply evt_cut; [eapply (mod_B_spec (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA)
      t0 t1 t2 a6 (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6 F fc mA
      (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (sa_msz SZ)) P (sa_msz SZ) (Z_to_bv 64 sec_name) lo) | post_call asegs mA].
  all: rewrite ?RU, ?ESP.
  1-3: lia.
  1:{ unfold hide, img_hull_lo, img_hull_hi. right. lia. }
  1:{ exact MF. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  1:{ replace (bv_unsigned sp - 96 - 48)%Z with (bv_unsigned sp - 144)%Z by lia. exact ST. }
  1:{ unfold kHighShadowEnd. lia. }
  1-2: lia.
  1:{ exact MI. }
  hide_disj.
  unfold sa_retA. replace (ret_pc (Z_to_bv 64 0x19f860)) with (Z_to_bv 64 0x19f860) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite RU in PC. destruct (zero_split32 _ P (sa_msz SZ) ltac:(lia) PC) as [HD RMP]. clear PC. rewrite ESP in PC0.
  eapply (sa_p2 (Z_to_bv 64 (bv_unsigned sp - 96)) gp s4 s6 s7 s9 s10 s11 F fc _ P SZ TCX T nres n lo mm md shj1 shj2).
  1:{ pose proof (unbox _ HSZ2). lia. }
  1:{ exact (unbox _ HP). }
  1:{ exact (unbox _ GP0). }
  1:{ exact (unbox _ GT0). }
  1:{ exact (unbox _ GX0). }
  1:{ exact (unbox _ APT0). }
  1:{ exact (unbox _ APX0). }
  1:{ exact (unbox _ ATX0). }
  1:{ lia. }
  1:{ unfold sec_page, i_sec_page. exact PG. }
  1:{ unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold,
        g_got_real_memset, g_real_memset, musl_memset_entry, SHB, kHighMemEnd.
      refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption. }
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact KK|split; [exact TSD|exact T0]]]|exact TT]. }
  1:{ exact TS. }
  1:{ exact HD. }
  1:{ exact SH1. }
  1:{ rewrite (unbox _ SR7). exact SH2. }
  1:{ exact MX. }
  1:{ exact PAD. }
  1:{ exact NR. }
  1:{ rewrite ESP. exact PC0. }
  1:{ unfold kHighShadowEnd. lia. }
  1:{ rewrite ESP. lia. }
  1:{ rewrite ESP. lia. }
  1:{ assumption. }
  intros m2 ra2 t0' t1' t2' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' MU2 WM2 MI2 HDF SH1' SH2' TS' LW ST2.
  clear GX0 GX3 GX4 APX APX0 ATX ATX0.
  rewrite (unbox _ SR7) in SH2'.
  clear PG KI KK TSD T0 TT CF GOT GRM RM CP SHB0 HM THR HD SH1 SH2 MX PAD TS PC0 POST.
  unfold sa_W2 in MU2. rewrite ESP in MU2. change i_sec_mutex with 6723456%Z in MU2.
  transport_after_call asegs x13 m2 MU2 WM2. clear MU2 WM2.
  hide_disj.
  (* [comment removed for export] *)
  destruct (msb_exists (sa_msz SZ) ltac:(lia)) as (k & Hk & Hx).
  apply (sec_rw_app2 _ 6722888 [C8 (Z_to_bv 64 nres)] [C8 (Z_to_bv 64 n)]) in NR. destruct NR as [NR1 NR2].
  eapply (clz_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (Z_to_bv 64 (sa_msz SZ)) k nres _ NR1 Hk).
  1:{ rewrite unsigned_lit by lia. exact Hx. }
  intros a1'' a2'' a5'' a6''.
  apply (sec_rw_app2 _ P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] [C8 (Z_to_bv 64 0)]) in HDF.
  destruct HDF as [HD3 HI].
  rewrite ESP in ST2.
  rewrite <- (unbox _ SR7) in SH2'.
  eapply (K0 m2 ra2 t0' t1' t2' a1'' a2'' a5'' a6'' a7' t3' t4' t5' t6' k jf b jj w1 w2 w3 w4 ga gm bl).
  all: first [ assumption
             | (apply (sec_rw_app2 _ 6722888 [C8 (Z_to_bv 64 nres)] [C8 (Z_to_bv 64 n)]); split; assumption)
             | (unfold mm_gcells; repeat (split; [assumption|]); assumption)
             | (unfold sec_range, i_sec_range; exact SRG)
             | exact HI ].
Qed.
