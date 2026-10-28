(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_secalloc_math.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0 R_flushshadow R_secdealloc R_secdealloc_p3.
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
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p
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
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p
          end ].

Lemma sd_shad_facts : forall MB MSZ lo, (MB mod 4096 = 0)%Z -> (MSZ mod 4096 = 0)%Z -> (0 < MB)%Z -> (MB + MSZ <= lo)%Z ->
  (lo <= 2^47)%Z -> (0x7fff8000 <= shad MB /\ shad MB + MSZ / 8 <= 0x10007fff8000 /\ 8 * (MSZ / 8) = MSZ)%Z.
Proof.
  intros MB MSZ lo H1 H2 H3 H4 H5.
  assert (P8 : (MB = 8 * (512 * (MB / 4096)))%Z) by (pose proof (Z.div_mod MB 4096 ltac:(lia)); lia).
  assert (M8 : (MSZ = 8 * (512 * (MSZ / 4096)))%Z) by (pose proof (Z.div_mod MSZ 4096 ltac:(lia)); lia).
  set (p := (MB / 4096)%Z) in *. set (q := (MSZ / 4096)%Z) in *.
  assert (D1 : (MB / 8 = 512 * p)%Z) by (rewrite P8; replace (8 * (512 * p))%Z with ((512 * p) * 8)%Z by lia; apply Z.div_mul; lia).
  assert (D2 : (MSZ / 8 = 512 * q)%Z) by (rewrite M8; replace (8 * (512 * q))%Z with ((512 * q) * 8)%Z by lia; apply Z.div_mul; lia).
  unfold shad, SHB. rewrite D1, D2. clear D1 D2. clearbody p q. lia.
Qed.

Definition sd_W (sp MB MSZ PAB IDX LMB : Z) : list (Z * Z) :=
  ((shad MB, shad MB + MSZ / 8) :: (sp - 96, sp) :: sd_W1 sp PAB IDX LMB)%Z.

Definition sd_K1 (MB MSZ PAB nres n IDX LMB : Z) (ws : list word) (m : mem) : Prop :=
  sec_core m PAB nres (n - 1) /\ sec_pad m /\ sec_junk m /\ u64arr bsegs m PAB (upd ws (Z.to_nat IDX) (Z_to_bv 64 LMB))
  /\ rw_cells bsegs m (LMB + 24) [C8 (Z_to_bv 64 IDX)]
  /\ rw_cells bsegs m (shad MB) [CB (Z.to_nat (MSZ / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (MSZ / 8)))].

Definition sd_K (MB MSZ SZ PAB nres n IDX LMB T : Z) (ws : list word) (mu mud : word) (m : mem) : Prop :=
  sec_core m PAB nres (n - 1) /\ sec_pad m /\ sec_junk m /\ u64arr bsegs m PAB (upd ws (Z.to_nat IDX) (Z_to_bv 64 LMB))
  /\ rw_cells bsegs m (LMB + 24) [C8 (Z_to_bv 64 IDX)]
  /\ rw_cells bsegs m (T + 2888) [C8 (Z_to_bv 64 (bv_unsigned mu + 1)); C8 (Z_to_bv 64 (bv_unsigned mud + MSZ))].

Lemma secdealloc_A1_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (MB MSZ SZ IDX PAB nres n LMB LIDX TCX T lo : Z) (ws : list word) (mu mud : word)
    (shj : list byte),
  (MB mod 4096 = 0 /\ 65536 < MSZ /\ MSZ mod 4096 = 0)%Z ->
  gobj MB MSZ lo -> gobj PAB 0x800000 lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo ->
  (7131136 <= LMB /\ LMB + 32 <= lo /\ (LMB + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= LMB))%Z ->
  sapart MB MSZ PAB 0x800000 -> sapart LMB 32 PAB 0x800000 -> (LMB = MB \/ LMB + 32 <= MB \/ MB + MSZ <= LMB)%Z ->
  sapart MB MSZ T 4096 -> sapart MB MSZ TCX 0xa0 -> sapart T 4096 TCX 0xa0 -> sapart T 4096 PAB 0x800000 ->
  sapart TCX 0xa0 PAB 0x800000 -> sapart T 4096 LMB 32 -> sapart TCX 0xa0 LMB 32 ->
  (0 <= IDX < n /\ n <= nres /\ Z.of_nat (length ws) = nres /\ nres <= 2^20)%Z ->
  nth_error ws (Z.to_nat IDX) = Some (Z_to_bv 64 MB) -> nth_error ws (Z.to_nat (n - 1)) = Some (Z_to_bv 64 LMB) ->
  sec_page m -> sec_core m PAB nres n -> sec_pad m -> sec_junk m -> u64arr bsegs m PAB ws ->
  rw_cells bsegs m MB [C8 (Z_to_bv 64 MB); C8 (Z_to_bv 64 MSZ); C8 (Z_to_bv 64 SZ)] ->
  rw_cells bsegs m (MB + 24) [C8 (Z_to_bv 64 IDX)] -> rw_cells bsegs m (LMB + 24) [C8 (Z_to_bv 64 LIDX)] ->
  ps_cells m -> rel_cells m -> thread_cells TCX T m -> rw_cells bsegs m (T + 2888) [C8 mu; C8 mud] ->
  rw_cells bsegs m (shad MB) [CB (Z.to_nat (MSZ / 8)) shj] ->
  stk bsegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 96)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (sd_M_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB MSZ SZ TCX T lo mu mud
               (sd_W (bv_unsigned sp) MB MSZ PAB IDX LMB) (sd_K1 MB MSZ PAB nres n IDX LMB ws) m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 SEC) (Z_to_bv 64 GSTAT) (Z_to_bv 64 (MB + 4096)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5b8b0) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. intros HMB GM GA GT GX GL AMA ALA ALM AMT AMX ATX ATA AXA ATL AXL Hidx HWI HWL PG SC PAD SJ ARR HD HDI WLI
    PS REL TH TS SH ST HLOH HLO HSP MI.
  pose proof (munch_refl (sd_W (bv_unsigned sp) MB MSZ PAB IDX LMB) m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  eapply (sd_p1 ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m MB MSZ SZ IDX PAB nres n LMB LIDX lo ws).
  all: try first [ exact HMB | exact GM | exact GA | exact AMA | exact ALA | exact ALM | exact Hidx | exact HWI | exact HWL
                 | exact PG | exact SC | exact PAD | exact SJ | exact ARR | exact HD | exact HDI | exact WLI | exact ST | exact HLOH
                 | exact MI | lia ].
  intros m1 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MU1 WM1 MI1 FR1 ST1 PG1 SC1 PAD1 SJ1 ARR1 HD1 WLI1.
  clear PG SC PAD SJ ARR HD HDI WLI PG1.
  destruct SC1 as (CH1 & NR1 & MX1). change i_sec_chunks with 1522464%Z in CH1. change i_sec_nres with 1522504%Z in NR1.
  change i_sec_mutex with 1523072%Z in MX1.
  unfold sec_pad in PAD1. change (i_sec_mutex + 1)%Z with 1523073%Z in PAD1.
  destruct SJ1 as ((b & jj & w1 & w2 & w3 & w4 & SJA) & (bl & Hbl & SJB) & (ga & gm & SJC)).
  change i_sec_sorted with 1522520%Z in SJA. change i_sec_bylog with 1522560%Z in SJB. change i_gstat_alloc with 1523096%Z in SJC.
  pose proof HMB as HMB0.
  destruct HMB as (HMB1 & HMB2 & HMB3). destruct Hidx as (HI1 & HI2 & Hlen & HI4).
  pose proof GM as GM0. apply box in GM0.
  destruct GM as (GM1 & GM2 & GM3 & GM4). destruct GA as (GA1 & GA2 & GA3 & GA4).
  pose proof GT as GT0. pose proof GX as GX0. pose proof ATX as ATX0. pose proof AMT as AMT0. apply box in GT0, GX0, ATX0, AMT0.
  destruct GT as (GT1 & GT2 & GT3 & GT4). destruct GX as (GX1 & GX2 & GX3 & GX4). destruct GL as (GL1 & GL2 & GL3).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GM4' : (7131136 <= MB)%Z) by (destruct GM4; lia). clear GM4.
  assert (GA4' : (7131136 <= PAB)%Z) by (destruct GA4; lia). clear GA4.
  pose proof (sd_shad_facts MB MSZ lo HMB1 HMB3 GM1 GM2 ltac:(lia)) as (SR1 & SR2 & SR3).
  remember (MSZ / 8)%Z as ms8 eqn:E8. apply box in E8.
  apply box in HMB1, HMB3, HMB0.
  ps_cells_destr PS.
  pose proof REL as (R1 & R2 & R3). clear REL. unfold g_got_pagesize_cached, g_got_sealed, g_PageSizeCached in R1, R2, R3.
  destruct TH as ((KI & KK & TSD & T0) & TT).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main, tpA in KI, KK, TSD, T0.
  unfold sd_W, sd_W1 in MU. unfold sd_W1 in MU1.
  change i_sec_nres with 1522504%Z in MU, MU1. change i_sec_sorted with 1522520%Z in MU, MU1.
  change i_gstat_alloc with 1523096%Z in MU, MU1. change i_sec_mutex with 1523072%Z in MU, MU1.
  hide_disj.
  transport_after_call bsegs m m1 MU1 WM1. clear MU1 WM1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = (bv_unsigned sp - 32)%Z) by (apply unsigned_lit; lia).
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ MB MSZ 0 lo shj).
  all: rewrite ?ESP.
  1:{ unfold ps_args_ok, kLowMemEnd, kHighMemEnd, kHighShadowEnd. pose proof (unbox _ HMB1). pose proof (unbox _ HMB3).
      unfold hide in GM3. split; [Z.div_mod_to_equations; lia| lia]. }
  1:{ lia. }
  1:{ right. rewrite <- (unbox _ E8). lia. }
  1:{ rewrite <- (unbox _ E8). exact SH. }
  1:{ unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold,
        g_got_real_memset, g_real_memset, musl_memset_entry, SHB, kHighMemEnd.
      refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption. }
  1:{ exact ST1. }
  1:{ lia. }
  1:{ unfold kHighShadowEnd. lia. }
  1:{ assumption. }
  eapply evt_mono.
  1:{ eapply (sd_p3a ra s0 s1 s2 _ _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ sp gp F fc _ MB MSZ SZ TCX T lo mu mud).
      1:{ exact (unbox _ HMB0). }
      1:{ exact (unbox _ GM0). }
      1:{ exact (unbox _ GT0). }
      1:{ exact (unbox _ GX0). }
      1:{ unfold sd_mid. split; [exact FR1|].
          split; [match goal with H : stk bsegs _ lo _ |- _ => rewrite ?ESP in H; exact H end|].
          split; [exact HD1|]. split; [split; [assumption| split; assumption]|].
          split; [unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached; split; [exact R1| split; [exact R2| exact R3]]|].
          split; [|exact TS].
          unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
          split; [split; [exact KI|split; [exact KK|split; [exact TSD|exact T0]]]|exact TT]. }
      1:{ unfold kHighShadowEnd. lia. }
      1:{ lia. }
      1:{ lia. }
      1:{ assumption. } }
  lazymatch goal with H : rw_cells bsegs _ (shad MB) _ |- _ => rename H into SHZ end.
  intros ms' PO. unfold sd_M_post in PO.
  destruct PO as (x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & m3 & E & MU3 & WM3 & MI3 & MID3 & _).
  subst ms'.
  clear TS FR1 R1 R2 R3 KI KK TSD T0 TT CF GOT GRM RM CP SHB0 HM THR HD1.
  unfold sd_W3a in MU3.
  lazymatch type of MU3 with munch _ ?mm _ => transport_after_call bsegs mm m3 MU3 WM3 end. clear MU3 WM3.
  unfold sd_M_post. do 11 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact MID3|].
  unfold sd_K1. split; [split; [exact CH1| split; [exact NR1| exact MX1]]|]. split; [exact PAD1|].
  split; [unfold sec_junk; split; [do 6 eexists; exact SJA|]; split; [eexists; split; [exact Hbl| exact SJB]|];
          do 2 eexists; exact SJC|].
  split; [exact ARR1|]. split; [exact WLI1|]. exact SHZ.
Qed.

Lemma secdealloc_A2_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (MB MSZ SZ IDX PAB nres n LMB TCX T lo : Z) (ws : list word) (mu mud : word),
  (MB mod 4096 = 0 /\ 65536 < MSZ /\ MSZ mod 4096 = 0)%Z ->
  gobj MB MSZ lo -> gobj PAB 0x800000 lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo ->
  (7131136 <= LMB /\ LMB + 32 <= lo /\ (LMB + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= LMB))%Z ->
  sapart MB MSZ T 4096 -> sapart T 4096 TCX 0xa0 -> sapart T 4096 PAB 0x800000 -> sapart T 4096 LMB 32 ->
  (0 <= IDX < n /\ n <= nres /\ Z.of_nat (length ws) = nres /\ nres <= 2^20)%Z ->
  sd_mid sp ra s0 s1 s2 MB MSZ SZ TCX T lo mu mud m ->
  sd_K1 MB MSZ PAB nres n IDX LMB ws m ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 96)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (sd_A_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB MSZ lo
               (sd_W3 (bv_unsigned sp) MB MSZ T) (sd_K MB MSZ SZ PAB nres n IDX LMB T ws mu mud) m)
    (nret (MSsvc (sd_M_regs sp gp t0 t1 t2 MB MSZ a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 madv_ecall) (Z_to_bv 64 233) fc None m (seg_rom bsegs))
          (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 (pbeg (shad MB)), Z_to_bv 64 (pend (shad (MB + MSZ)) - pbeg (shad MB)))])).
Proof.
  intros until mud. intros HMB GM GA GT GX GL AMT ATX ATA ATL Hidx MID K1 HLOH HLO HSP MI.
  destruct K1 as ((CH1 & NR1 & MX1) & PAD1 & SJ1 & ARR1 & WLI1 & _).
  change i_sec_chunks with 1522464%Z in CH1. change i_sec_nres with 1522504%Z in NR1. change i_sec_mutex with 1523072%Z in MX1.
  unfold sec_pad in PAD1. change (i_sec_mutex + 1)%Z with 1523073%Z in PAD1.
  destruct SJ1 as ((b & jj & w1 & w2 & w3 & w4 & SJA) & (bl & Hbl & SJB) & (ga & gm & SJC)).
  change i_sec_sorted with 1522520%Z in SJA. change i_sec_bylog with 1522560%Z in SJB. change i_gstat_alloc with 1523096%Z in SJC.
  eapply evt_mono.
  1:{ eapply (sd_p3b ra s0 s1 s2 t0 t1 t2 a4 a5 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp gp F fc m MB MSZ SZ TCX T lo mu mud);
      first [ eassumption | lia ]. }
  intros ms' PO. unfold sd_A_post in PO.
  destruct PO as (x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & m3 & E & MU3 & WM3 & MI3 & UF3 & ST3 & TS3).
  subst ms'.
  destruct HMB as (HMB1 & HMB2 & HMB3). destruct Hidx as (HI1 & HI2 & Hlen & HI4).
  destruct GM as (GM1 & GM2 & GM3 & GM4). destruct GA as (GA1 & GA2 & GA3 & GA4).
  destruct GT as (GT1 & GT2 & GT3 & GT4). destruct GX as (GX1 & GX2 & GX3 & GX4). destruct GL as (GL1 & GL2 & GL3).
  pose proof (sd_hull_facts MB MSZ lo HMB1 HMB3 HMB2 GM1 GM2 ltac:(unfold kHighShadowEnd in *; lia)) as (HF1 & HF2 & HF3 & HF4 & HF5 & HF6).
  unfold sapart, img_hull_lo, img_hull_hi, kHighShadowEnd in *.
  assert (GA4' : (7131136 <= PAB)%Z) by (destruct GA4; lia). clear GA4.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  clear MID. pose proof MU3 as MU3'. unfold sd_W3 in MU3.
  assert (HPB : (2147450880 <= pbeg (shad MB))%Z) by lia.
  assert (HPE : (pend (shad (MB + MSZ)) <= 17594333495296)%Z) by lia.
  clear HF1 HF2 HF4 HF5 HF6.
  set (PB := pbeg (shad MB)) in MU3, HPB, HF3. set (PE := pend (shad (MB + MSZ))) in MU3, HPE, HF3. clearbody PB PE.
  apply box in HMB1, HMB3.
  hide_disj.
  transport_after_call bsegs m m3 MU3 WM3.
  unfold sd_A_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU3'|]. split; [assumption|]. split; [exact MI3|]. split; [exact UF3|]. split; [exact ST3|].
  unfold sd_K. split; [split; [exact CH1| split; [exact NR1| exact MX1]]|]. split; [exact PAD1|].
  split; [unfold sec_junk; split; [do 6 eexists; exact SJA|]; split; [eexists; split; [exact Hbl| exact SJB]|];
          do 2 eexists; exact SJC|].
  split; [exact ARR1|]. split; [exact WLI1| exact TS3].
Qed.
