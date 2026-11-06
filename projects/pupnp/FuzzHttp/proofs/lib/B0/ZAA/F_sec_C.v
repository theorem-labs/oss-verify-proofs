(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout ATacA PEnv LJ LJU F_mm_A F_poison F_flush APrim F_prim_L0 AFrame ASec ASecD SecBits F_sec_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition sec_dealloc_entry : Z := 0x35e64.

Local Ltac dj_rec ::=
  first [ exact I | assumption
        | lazymatch goal with |- _ /\ _ => split; [dj_rec | dj_rec] end
        | lia
        | match goal with D : disjoint_from ?W ?A0 ?n0 |- disjoint_from ?W ?A ?n => apply (disjoint_from_sub W A0 n0 A n D); lia end ].
Local Ltac sub_fp_solve ::=
  unfold sub_fp; cbn [outside]; let xo := fresh "xo" in let Ho := fresh "Ho" in intros xo Ho; destruct_ands Ho;
  repeat split; lia1.
Local Ltac transport_after_call_fk segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping stk hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      let J := fresh "MUj" in pose proof (munch_join Wq W mq m m' H MU) as J; clear H; rename J into H; cbn [List.app] in H
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fk segs m m' MU WM.

Section FR.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation PARR := (al_parr AL).

#[using="Type"] Lemma thread_env_frame_but : forall L W m m',
  thread_env L m -> munch W m m' -> wmono_but W m m' -> thread_clear2 L W -> thread_env L m'.
Proof.
  intros L W m m' TE MU WB F. unfold thread_clear2 in F. te_split TE. unfold thread_env.
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_but C MU WB F end.
Qed.

#[using="Type"] Lemma RSEC_frame_but : forall S W m m',
  RSEC AL S m -> munch W m m' -> wmono_but W m m' ->
  Forall (fun iv : Z * Z => snd iv <= 0x10000 \/ 0x609000 <= fst iv) W ->
  0 <= PARR -> disjoint_from W PARR (2^23) ->
  Forall (fun d => disjoint_from W (sc_beg d) 32) (se_chunks S) -> RSEC AL S m'.
Proof.
  intros S W m m' (WF & (ENV & ENV2 & ENV3) & VARS & PR & HD) MU WB F P0 DP DH.
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS).
  pose proof WF as (W0 & _ & W2 & _).
  assert (DI : forall A n, 0x10000 <= A -> A + n <= 0x609000 -> disjoint_from W A n).
  { intros A n HA HN. apply dj_of_Forall. eapply Forall_impl; [| exact F]. intros [lo' hi'] Hiv; cbn in Hiv |- *. lia. }
  unfold RSEC. split; [exact WF|]. split; [| split; [| split]].
  - split; [| split]; (eapply rw_cells_transport_but; [exact MU| exact WB| eassumption| apply DI; cbn; lia]).
  - unfold sec_vars. split; [| split; [| split]].
    + exists j24, j32, j40, jsb, jpad, na, nf, cur, mx. eapply rw_cells_transport_but; [exact MU| exact WB| exact VC| apply DI; cbn; lia].
    + exists bsl. split; [| exact LBSL]. eapply u64arr_transport_but; [exact MU| exact WB| exact BSL|]. rewrite LBSL. apply DI; cbn; lia.
    + eapply rw_cells_transport_but; [exact MU| exact WB| exact MTX| apply DI; cbn; lia].
    + exists g16, g24. eapply rw_cells_transport_but; [exact MU| exact WB| exact GST| apply DI; cbn; lia].
  - exists ws. split; [| split; [exact LWS| exact FWS]].
    eapply u64arr_transport_but; [exact MU| exact WB| exact PARRu|].
    eapply disjoint_from_sub; [exact DP| lia| lia].
  - intros j d Hj. eapply rw_cells_transport_but; [exact MU| exact WB| exact (HD j d Hj)|].
    cbn. exact (proj1 (Forall_forall _ _) DH d (nth_error_In _ _ Hj)).
Qed.

#[using="Type"] Lemma hdrs_rep_dealloc : forall (S0 : asec) (i0 : nat) (lastc0 : schunk) W (m0 m' : word -> option byte),
  hdrs_rep S0 m0 -> (i0 < length (se_chunks S0))%nat -> nth_error (se_chunks S0) (length (se_chunks S0) - 1) = Some lastc0 ->
  munch W m0 m' -> wmono asegs m0 m' ->
  (forall j d, nth_error (se_chunks S0) j = Some d -> j <> i0 -> j <> (length (se_chunks S0) - 1)%nat -> disjoint_from W (sc_beg d) 32) ->
  (i0 <> (length (se_chunks S0) - 1)%nat -> rw_cells asegs m' (sc_beg lastc0) (hdr_cells lastc0 (Z.of_nat i0))) ->
  hdrs_rep (sec_dealloc S0 i0) m'.
Proof.
  intros S0 i0 lastc0 W m0 m' HD0 IL0 NL0 MU0 WM0 DJ HL j d Hj. unfold sec_dealloc in Hj. cbn [se_chunks] in Hj.
  destruct (remove_at_src _ i0 j d IL0 Hj) as [Lj Sj].
  destruct (Nat.eqb_spec j i0) as [->|NE].
  - rewrite NL0 in Sj. injection Sj as <-. apply HL. lia.
  - eapply rw_cells_transport; [exact (HD0 j d Sj)| exact MU0| exact WM0|]. cbn. apply (DJ j d Sj NE). lia.
Qed.

End FR.

Section SD.
Context {HC : HasCeiling}.
Variable E : penv.
Variable AL : alayout.
Notation L := (al_thread AL).
Notation PARR := (al_parr AL).

Definition sec_dealloc_tree (c : schunk) : itree nodeL (exc unit) :=
  ebind (poison_tree (sc_beg c) (sc_msize c) 0)
        (fun _ => ebind (flush_tree (sc_beg c) (sc_msize c)) (fun _ => t_unmap (sc_beg c) (sc_msize c))).

Definition sec_dealloc_H (c : schunk) (H : word -> bool) : word -> bool :=
  unhide_range (sc_beg c) (sc_beg c + sc_msize c) (flush_H (sc_beg c) (sc_msize c) (poison_H (sc_beg c) (sc_msize c) 0 H)).

Definition sec_last (S : asec) (c : schunk) : schunk := nth (length (se_chunks S) - 1) (se_chunks S) c.

Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (q lo : Z) (m : word -> option byte) (H : word -> bool) (S : asec) (i : nat) (c : schunk).

Notation BEG := (sc_beg c).
Notation MSZ := (sc_msize c).
Notation LASTB := (sc_beg (sec_last S c)).

Definition sec_dealloc_post : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = sec_dealloc_H c H
    /\ munch [(q - 624, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
              (BEG, BEG + MSZ); (sh BEG, sh BEG + MSZ / 8); (LASTB, LASTB + 32)] m m'
    /\ wmono_but [(BEG, BEG + MSZ); (sh BEG, sh BEG + MSZ / 8)] m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ RSEC AL (sec_dealloc S i) m'
    /\ (exists ts, rw_cells asegs m' (at_thr L + 2800) [CB 368 ts])
    /\ flush_edges BEG MSZ m'.

#[using="Type"] Lemma sec_dealloc_B : forall (mB : word -> option byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (ts junk : list byte),
  mem_inv asegs mB -> mclean H mB -> poison_env E mB -> thread_env L mB -> thread_layout_ok L -> alayout_ok AL ->
  RSEC AL (sec_dealloc S i) mB -> chunk_ok AL c ->
  Forall (fun d => apart_chunks c d) (se_chunks (sec_dealloc S i)) ->
  rw_cells asegs mB BEG (hdr_cells c (Z.of_nat i)) ->
  rw_cells asegs mB (at_thr L + 2800) [CB 368 ts] ->
  rw_cells asegs mB (sh BEG) [CB (Z.to_nat (MSZ / 8)) junk] ->
  stk asegs mB lo (q - 32) -> alloc_ceiling <= lo -> lo <= q - 624 -> q mod 16 = 0 -> q <= 2^47 ->
  rw_cells asegs mB (q - 32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(q - 624, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (at_thr L + 2800, at_thr L + 3168); (PARR, PARR + 2^23);
         (BEG, BEG + MSZ); (sh BEG, sh BEG + MSZ / 8); (LASTB, LASTB + 32)] m mB ->
  wmono asegs m mB ->
  evt asegs (lzk H (sec_dealloc_tree c) sec_dealloc_post)
    (MS (mkR ra (wz (q - 32)) gp (wz A0_TP) t0 t1 t2 (wz BEG) s1 (wz SEC) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x35f40) fc None mB (seg_rom asegs)).
Proof.
  intros until junk. intros MI C PE TE TL AO RS CK SEPc HDRc TS SHC STc CLO LOQ Q16 QHI FR MU WM.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (@alloc_ceiling_lt47 HC) as C47.
  pose proof (chunk_ok_msize AL c CK) as [CM1 CM2].
  pose proof CK as (CK1 & CK2 & CK3 & _ & CK5 & CK6 & CK7).
  pose proof TL as (T1 & T2 & T3 & T4 & T5 & _).
  unfold al_regions in CK7.
  apply Forall_cons_iff in CK7 as [_ CK7]. apply Forall_cons_iff in CK7 as [CP CK7].
  apply Forall_cons_iff in CK7 as [CC CK7]. apply Forall_cons_iff in CK7 as [CT _].
  cbn [fst snd] in CP, CC, CT. unfold apart in CP, CC, CT.
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _ & P4 & P5 & _ & _).
  layout_apart_fact AO 1%nat 2%nat LP2. layout_apart_fact AO 1%nat 3%nat LP3.
  demod CK1 bz. demod CM2 mz. demod Q16 qz.
  assert (ED : MSZ / 8 = 512 * mz) by (rewrite CM2; clear; Z.div_mod_to_equations; lia).
  assert (SHR : 0x7fff8000 <= sh BEG /\ sh BEG + 512 * mz <= 0x10007fff8000)
    by (unfold sh, SHADOW_OFF; clear - CK1 CK2 CM2 CM1 CK6 C47; Z.div_mod_to_equations; nia).
  assert (LZ : lenZ MSZ = MSZ) by (rewrite lenZ_mmap_len by lia; unfold mmap_len, page_round_up_Z, page_size; clear - CM2 CM1; Z.div_mod_to_equations; nia).
  unfold hdr_cells in HDRc.
  pose proof (munch_refl [(q - 624, q); (at_thr L + 2800, at_thr L + 3168)] mB) as MUB. pose proof (wmono_refl asegs mB) as WMB.
  hide CP; hide CC; hide LP2; hide LP3; hide T5; hide CK5.
  assert (RSH : BEG + MSZ <= sh BEG \/ sh BEG + 512 * mz <= BEG) by (unhide CK5; clear - CK5 SHR; lia).
  do 2 zstep.
  do 3 zstep.
  zstep.
  assert (QB : 0x10007fff8000 <= lo /\ lo <= q - 32 - 64 /\ q - 32 <= 2^47) by (clear - CLO ACR LOQ QHI; lia).
  assert (AB : BEG mod 8 = 0 /\ MSZ mod 8 = 0 /\ 0 <= MSZ /\ poison_range BEG MSZ /\ 0 <= 0 < 256).
  { unhide CK5. unfold poison_range. clear - CK1 CM2 CM1 CK2 CK5 CK6 C47.
    split; [rewrite CK1; replace (bz * 4096) with (bz * 512 * 8) by lia; apply Z_mod_mult|].
    split; [rewrite CM2; replace (mz * 4096) with (mz * 512 * 8) by lia; apply Z_mod_mult|]. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      callA (poison_shadow_specA E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 32) lo BEG MSZ 0 mm MIx QB AB H ltac:(clear - LOQ; lia) _ _ _ _ _ junk);
      [ assumption | exact PE | exact STc | exact SHC | ] end end.
  rename PC into STc. rename PC0 into PEc. rename POST into SHZ.
  do 2 zstep.
  zstep.
  cbv beta.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      callAb (flush_shadow_specA E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm H (q - 32) lo BEG MSZ MIx);
      [ assumption | exact PEc | exact STc | clear - CLO ACR LOQ QHI; lia | clear - LOQ; lia | clear - QHI; lia | reflexivity | reflexivity
      | clear - CM1; lia | exact CK2 | exact (proj1 AB) | exact (proj1 (proj2 AB))
      | unhide CK5; clear - CK5 CK6 C47; lia | exact SHZ | ] end end.
  clear PEc. rename PC into STc. rename PC0 into PEc. rename POST into SHZ.
  rewrite ED in *. clear ED.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mF end.
  pose proof (wmono_refl asegs mF) as WMR. pose proof (munch_refl [(q - 624, q); (at_thr L + 2800, at_thr L + 3168)] mF) as MUR.
  rename PEc into PEF.
  lazymatch type of MUB with munch ?Wb _ _ => assert (WBB : wmono_but Wb mB mF) by (eapply wmono_but_weaken; [| exact WMB]; clear; sub_fp_solve) end.
  pose proof (thread_env_frame_but L _ mB mF TE MUB WBB ltac:(unhide CC; unhide T5; clear - CC CT T1 T2 T3 T4 T5 CLO LOQ QHI SHR ACR;
        unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia)) as TEc.
  clear WBB.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (gcts_spec L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 32) mm lo _ _);
      [exact STc| exact CLO| clear - LOQ; lia| clear - Q16; rewrite Q16; replace (qz * 16 - 32) with ((qz - 2) * 16) by lia; apply Z_mod_mult| clear - QHI; lia| exact TEc| exact TL| exact MIx|] end end.
  clear TEc. rename PC into STc. rename POST into TEc.
  do 4 zstep.
  do 2 zstep.
  do 2 zstep.
  do 2 zstep.
  do 4 zstep.
  zstep. replace (q - 32 + 32) with q by lia.
  zstep.
  release_frame FR STc q.
  destruct (rw_cells_forget _ _ _ _ TS) as [ts' TS']. cbn [cells_size csize Nat.add] in TS'. clear TS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (poison_env_frame2 E _ mF mm PEF MUR WMR ltac:(clear - LOQ CLO ACR T3 SHR; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia)) as PEf end.
  lz_here.
  cbv beta.
  eapply implA_mono.
  { eapply (unmap_or_die_spec E); [ assumption | exact MC | exact PEf | exact STc | clear - CLO ACR; lia | clear - LOQ; lia | exact QHI
      | reflexivity | reflexivity | rewrite CK1; apply Z_mod_mult | exact CK2 | clear - CM1 CK6 C47 CK2; lia | rewrite LZ; clear - CK6 C47; lia
      | left; rewrite LZ; clear - CK6 CLO; lia ]. }
  intros u H' ms' (y10 & y11 & y12 & y13 & y17 & m' & EM & EH & MUu & WBu & MIu & STu & PEu).
  rewrite LZ in EH, MUu, WBu.
  unfold sec_dealloc_post. subst ms' H'.
  do 16 eexists. split; [reflexivity|].
  split; [reflexivity|].
  pose proof (munch_join _ _ _ _ _ MU MUu) as MUT. pose proof (munch_join _ _ _ _ _ MUB MUu) as MUBT. cbn [List.app] in MUT, MUBT.
  assert (ED : MSZ / 8 = 512 * mz) by (rewrite CM2; clear; Z.div_mod_to_equations; lia). rewrite ED.

  assert (WBm : wmono_but [(sh BEG, sh BEG + 512 * mz); (BEG, BEG + MSZ)] m m')
    by exact (wmono_but_join _ _ _ _ _ (wmono_but_wmono_r _ _ _ _ WM WMR) WBu).
  assert (WBb : wmono_but [(sh BEG, sh BEG + 512 * mz); (BEG, BEG + MSZ)] mB m')
    by exact (wmono_but_join _ _ _ _ _ (wmono_but_wmono_r _ _ _ _ WMB WMR) WBu).
  lazymatch type of MUBT with munch ?Wt _ _ => assert (WBT : wmono_but Wt mB m') by (eapply wmono_but_weaken; [| exact WBb]; clear; sub_fp_solve) end.
  assert (WBU : wmono_but [(q - 48, q); (BEG, BEG + MSZ)] m1 m') by (eapply wmono_but_weaken; [| exact WBu]; clear; sub_fp_solve).
  split. { refine (munch_weaken _ _ _ _ _ MUT). clear - LOQ. sub_fp_solve. }
  split. { eapply wmono_but_weaken; [| exact WBm]. clear. sub_fp_solve. }
  split; [exact MIu|]. split; [exact STu|]. split; [exact PEu|].
  split. { eapply (thread_env_frame_but L _ mB m' TE MUBT WBT). unhide CC; unhide T5.
           clear - CC CT T1 T2 T3 T4 T5 CLO LOQ QHI SHR ACR CK2 CM1.
           unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia. }
  split.
  { eapply (RSEC_frame_but AL _ _ mB m' RS MUBT WBT).
    - clear - LOQ CLO ACR T3 SHR CK2. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia.
    - clear - P1; lia.
    - unhide CP; unhide LP3. clear - CP LP3 P1 P2 SHR CLO LOQ. cbn [disjoint_from]. repeat split; lia.
    - destruct RS as ((_ & _ & _ & _ & _ & WD5 & _) & _).
      apply Forall_forall. intros d Hd.
      pose proof (proj1 (Forall_forall _ _) WD5 d Hd) as CKd.
      pose proof (chunk_ok_msize AL d CKd) as [DM1 _].
      destruct CKd as (_ & D2 & _ & _ & D5 & D6 & D7).
      unfold al_regions in D7. apply Forall_cons_iff in D7 as [_ D7]. apply Forall_cons_iff in D7 as [_ D7].
      apply Forall_cons_iff in D7 as [_ D7]. apply Forall_cons_iff in D7 as [DT _]. cbn [fst snd] in DT. unfold apart in DT.
      pose proof (proj1 (Forall_forall _ _) SEPc d Hd) as AP. unfold apart_chunks in AP.
      clear - D2 D5 D6 DT DM1 AP SHR CLO LOQ. cbn [disjoint_from]. repeat split; lia. }
  split.
  { exists ts'. eapply (rw_cells_transport_but _ m1 m' MUu WBU); [exact TS'|].
    clear - CT T3 T4 CLO LOQ. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }

  assert (TRE : forall A k (bs : list byte), rw_cells asegs mF A [CB (Z.to_nat k) bs] -> 0 <= k -> sh BEG <= A -> A + k <= sh BEG + 512 * mz ->
                rw_cells asegs m' A [CB (Z.to_nat k) bs]).
  { intros A k bs X K0 D1 D2.
    eapply (rw_cells_transport_but _ m1 m' MUu WBU).
    - eapply (rw_cells_transport asegs _ mF m1); [exact X| exact MUR| exact WMR|].
      cbn [cells_size csize disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by exact K0. clear - D1 D2 SHR CLO LOQ T3 T4. repeat split; lia.
    - cbn [cells_size csize disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by exact K0. clear - D1 D2 SHR RSH CLO LOQ QB. repeat split; lia. }
  assert (SHE : sh (BEG + MSZ) = sh BEG + 512 * mz) by (unfold sh; clear - CK1 CM2; Z.div_mod_to_equations; lia).
  unfold flush_edges, flush_range in SHZ |- *. rewrite ED in SHZ |- *.
  pose proof (fl_pgup_ge (sh BEG)) as G1. pose proof (fl_pgdn_le (sh (BEG + MSZ))) as G2. rewrite SHE in G2 at 2.
  set (pb := pgup (sh BEG)) in *. set (pe := pgdn (sh (BEG + MSZ))) in *.
  destruct (pe <=? pb) eqn:EF.
  - apply TRE; [exact SHZ| clear - CM1 CM2; lia| clear; lia| clear; lia].
  - apply Z.leb_gt in EF. destruct SHZ as [S1 S3].
    replace (pb + (pe - pb)) with pe in S3 |- * by (clear; lia).
    split; apply TRE; try assumption; clear - G1 G2 EF; lia.
Qed.

#[using="Type"] Lemma sec_dealloc_spec : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ts junk : list byte),
  mem_inv asegs m -> mclean H m -> poison_env E m -> thread_env L m -> thread_layout_ok L -> alayout_ok AL ->
  RSEC AL S m -> nth_error (se_chunks S) i = Some c ->
  rw_cells asegs m (at_thr L + 2800) [CB 368 ts] ->
  rw_cells asegs m (sh BEG) [CB (Z.to_nat (MSZ / 8)) junk] ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 624 -> q mod 16 = 0 -> q <= 2^47 ->
  implA H (sec_dealloc_tree c) sec_dealloc_post
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz SEC) (wz GSTATS) (wz (BEG + 4096)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz sec_dealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI C PE TE TL AO RS NTH TS SHC ST CLO LOQ Q16 QHI. unfold sec_dealloc_entry.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (@alloc_ceiling_lt47 HC) as C47.
  destruct RS as (WF & (ENV & ENV2 & ENV3) & VARS & PR & HD).
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS).
  pose proof WF as (W0 & W1 & W2 & W3 & W4 & W5 & W6).
  pose proof (nth_error_lt _ _ _ NTH) as IL.
  assert (NL : nth_error (se_chunks S) (length (se_chunks S) - 1) = Some (sec_last S c)) by (unfold sec_last; apply nth_error_nth'; lia).
  remember (sec_last S c) as lastc eqn:ELAST.
  pose proof (proj1 (Forall_forall _ _) W5 c (nth_error_In _ _ NTH)) as CK.
  pose proof (proj1 (Forall_forall _ _) W5 lastc (nth_error_In _ _ NL)) as CKL.
  pose proof (chunk_ok_msize AL c CK) as [CM1 CM2]. pose proof (chunk_ok_msize AL lastc CKL) as [LM1 _].
  pose proof CK as (CK1 & CK2 & _ & _ & CK5 & CK6 & CK7).
  pose proof CKL as (_ & L2 & _ & _ & L5 & L6 & L7).
  unfold al_regions in CK7, L7.
  apply Forall_cons_iff in CK7 as [_ CK7]. apply Forall_cons_iff in CK7 as [CP CK7].
  apply Forall_cons_iff in CK7 as [CC CK7]. apply Forall_cons_iff in CK7 as [CT _].
  apply Forall_cons_iff in L7 as [_ L7]. apply Forall_cons_iff in L7 as [LP _].
  cbn [fst snd] in CP, CC, CT, LP. unfold apart in CP, CC, CT, LP.
  pose proof TL as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _ & P4 & P5 & _ & _).
  layout_apart_fact AO 1%nat 2%nat LP2. layout_apart_fact AO 1%nat 3%nat LP3.
  pose proof (HD i c NTH) as HDRc. pose proof (HD _ lastc NL) as HDRl. unfold hdr_cells in HDRc, HDRl.
  set (n := length (se_chunks S)) in *.
  assert (SN : se_n S = Z.of_nat n) by reflexivity.
  assert (WI : nth_error ws i = Some (wz BEG)).
  { pose proof (f_equal (fun x => nth_error x i) FWS) as X. cbn beta in X.
    rewrite nth_error_firstn, nth_error_map, NTH in X. replace (i <? n)%nat with true in X by (symmetry; apply Nat.ltb_lt; lia). exact X. }
  assert (WLs : nth_error ws (n - 1) = Some (wz (sc_beg lastc))).
  { pose proof (f_equal (fun x => nth_error x (n - 1)%nat) FWS) as X. cbn beta in X.
    rewrite nth_error_firstn, nth_error_map, NL in X. replace (n - 1 <? n)%nat with true in X by (symmetry; apply Nat.ltb_lt; lia). exact X. }
  demod CK1 bz. demod CM2 mz.
  hide CP; hide CC; hide CT; hide LP; hide LP2; hide LP3; hide T5; hide CK5; hide L5; hide W1; hide Q16; hide SHC; hide TS.
  pose proof (munch_refl [(q - 32, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (PARR, PARR + 2^23); (sc_beg lastc, sc_beg lastc + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM. pose proof MI as MI0. hide MI0.
  carve_frame 32%nat ST.
  lz_go.
  do 5 zstep.
  zstep.
  do 2 zstep.
  replace (Z.land 4095 (BEG + 4096)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; clear - CK1 CK2; Z.div_mod_to_equations; lia).
  zstep. if_false.
  do 4 zstep.
  unfold b8 in MTX.
  amo_step.   try fold_cb_load.
  do 4 zstep.
  amo_step.
  zstep. if_false.
  zstep.
  zstep.
  replace (BEG + 4096 - 4096) with BEG by lia.
  zstep. if_false.
  zstep.
  zstep.
  do 2 zstep.
  rewrite (Z.shiftl_mul_pow2 (Z.of_nat i) 3) by lia. change (2 ^ 3) with 8.
  replace (PARR + Z.of_nat i * 8) with (PARR + 8 * Z.of_nat i) by lia.
  pose proof (u64arr_read asegs _ PARR ws (Z.of_nat i) (wz BEG) (wa (PARR + 8 * Z.of_nat i)) PARRu ltac:(rewrite Nat2Z.id; exact WI) ltac:(lia) eq_refl) as RDI.
  zstep.
  zstep. if_false_z.
  zstep.
  zstep. if_false_z.
  zstep.
  zstep.
  zstep.
  do 2 zstep.
  zstep.
  rewrite (Z.shiftl_mul_pow2 (se_n S) 3) by lia. change (2 ^ 3) with 8.
  replace (se_n S * 8 + PARR) with (PARR + 8 * Z.of_nat (n - 1) + 8) by lia.
  pose proof (u64arr_read asegs _ PARR ws (Z.of_nat (n - 1)) (wz (sc_beg lastc)) (wa (PARR + 8 * Z.of_nat (n - 1))) PARRu ltac:(rewrite Nat2Z.id; exact WLs) ltac:(lia) eq_refl) as RDL.
  zstep.
  do 2 zstep.
  zstep.
  sstep.
  do 2 zstep.
  do 2 zstep.
  pose proof (u64arr_store_ok asegs _ PARR ws (Z.of_nat i) (wa (PARR + 8 * Z.of_nat i)) PARRu ltac:(lia) eq_refl) as SOK.
  unhide CP; unhide LP.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
    pose proof (u64arr_write asegs mx PARR ws (Z.of_nat i) (wz (sc_beg lastc)) PARRu ltac:(lia)) as PARRu2 end.
  clear PARRu SOK. store_done. rename PARRu2 into PARRu.
  hide CP; hide LP.
  destruct (Nat.eq_dec i (n - 1)) as [EI|NEI];
    [ assert (EC : lastc = c) by (rewrite <- EI in NL; congruence); clear HDRl; rewrite EC in *
    | pose proof (chunks_sep_nth _ W6 i (n - 1)%nat c lastc NEI NTH NL) as APL; unfold apart_chunks in APL ].
  all: unhide LP; unhide CP.
  all: zstep.
  all: hide LP; hide CP.
  all: amo_step.
  all: zstep.
  all: do 2 zstep.
  all: amo_step.
  all: zstep.
  all: lazymatch type of MTX with rw_cells _ ?mm _ _ =>
    assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
      by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
          lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
          cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
    clear MTX end.
  all: sstep.
  all: replace (q + -32) with (q - 32) in * by lia.
  all: unhide SHC; unhide TS.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport asegs _ m mm _ _ SHC MU WM) as SHC';
    pose proof (rw_cells_transport asegs _ m mm _ _ TS MU WM) as TS';
    pose proof (poison_env_frame2 E _ m mm PE MU WM) as PEf;
    pose proof (thread_env_frame2 L _ m mm TE MU WM) as TEf end.
  all: assert (ED : MSZ / 8 = 512 * mz) by (rewrite CM2; clear; Z.div_mod_to_equations; lia).
  all: assert (SHR : 0x7fff8000 <= sh BEG /\ sh BEG + 512 * mz <= 0x10007fff8000)
         by (unfold sh, SHADOW_OFF; clear - CK1 CK2 CM2 CM1 CK6 C47; Z.div_mod_to_equations; nia).
  all: pose proof CKL as (_ & _ & _ & _ & _ & _ & L7'); unfold al_regions in L7';
       apply Forall_cons_iff in L7' as [_ L7']; apply Forall_cons_iff in L7' as [_ L7'];
       apply Forall_cons_iff in L7' as [LC L7']; apply Forall_cons_iff in L7' as [LT _];
       cbn [fst snd] in LC, LT; unfold apart in LC, LT.
  all: specialize (SHC' ltac:(unhide L5; clear - L5 L6 LM1 SHR ED CLO LOQ P1 CM1 CM2 ACR; cbn [disjoint_from cells_size csize Nat.add];
                               rewrite Nat.add_0_r, Z2Nat.id by lia; rewrite ED; repeat split; lia)).
  all: specialize (PEf ltac:(clear - LOQ CLO ACR P1 L2; unfold sec_clear; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia)).
  all: specialize (TEf ltac:(unhide LP2; unhide LP3; clear - LP2 LP3 LC LT LM1 T1 T2 T3 T4 CLO LOQ QHI ACR P1 L2;
                              unfold thread_clear2; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; repeat split; lia)).
  all: specialize (TS' ltac:(unhide LP3; clear - LP3 LT LM1 T3 T4 CLO LOQ ACR; cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia)).
  all: lz_here.
  all: eapply implA_go_clean; [exact MC|].
  all: assert (MIf : mem_inv asegs m1)
         by (unhide MI0; refine (mem_inv_munch_above _ m m1 MI0 MU _); clear - LOQ CLO ACR P1 L2;
             repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; lia).
  all: eapply (sec_dealloc_B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ts junk);
    [ exact MIf | exact MC | exact PEf | exact TEf | exact TL | exact AO
    |
    | exact CK | apply remove_at_apart; [exact W6| exact NTH]
    | exact HDRc | exact TS' | exact SHC' | exact ST | exact CLO | exact LOQ | unhide Q16; exact Q16 | exact QHI | exact FR
    | rewrite <- ELAST; refine (munch_weaken _ _ _ _ _ MU); clear - LOQ; sub_fp_solve
    | exact WM ].
  all: unfold RSEC; split; [exact (sec_wf_dealloc AL S i WF IL)|]; split; [split; [exact ENV| split; [exact ENV2| exact ENV3]]|]; split; [| split].
  all: try lazymatch goal with |- sec_vars _ _ =>
    unfold sec_vars, sec_dealloc, se_n; cbn [se_chunks se_nres]; rewrite remove_at_length by exact IL; fold n;
    replace (Z.of_nat (n - 1)) with (se_n S + -1) by lia;
    split; [exists j24, j32, j40; eexists _, jpad, na, _, _, mx; exact VC|];
    split; [exists bsl; split; [exact BSL| exact LBSL]|];
    split; [| eexists _, _; exact GST] end.
  all: try lazymatch goal with |- rw_cells asegs _ 725376 _ =>
    lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
      destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
      lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
      cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end end.
  all: try lazymatch goal with |- parr_rep _ _ _ =>
    rewrite Nat2Z.id in PARRu;
    eexists; split; [exact PARRu|]; unfold sec_dealloc, se_n; cbn [se_chunks se_nres];
    split; [rewrite upd_length; exact LWS|];
    rewrite remove_at_length by exact IL;
    exact (parr_prefix_remove (fun c0 => wz (sc_beg c0)) (se_chunks S) ws i _ IL ltac:(fold n; lia) FWS NL) end.
  all: refine (hdrs_rep_dealloc S i _ _ m m1 HD IL NL MU WM _ _);
    [ intros j d Hj NJ NJL;
      pose proof (proj1 (Forall_forall _ _) W5 d (nth_error_In _ _ Hj)) as CKd;
      pose proof (chunk_ok_msize AL d CKd) as [DM1 _];
      destruct CKd as (_ & D2 & _ & _ & _ & D6 & D7);
      unfold al_regions in D7; apply Forall_cons_iff in D7 as [_ D7]; apply Forall_cons_iff in D7 as [DP _];
      cbn [fst snd] in DP; unfold apart in DP;
      pose proof (chunks_sep_nth _ W6 j (n - 1)%nat d _ NJL Hj NL) as APd; unfold apart_chunks in APd;
      clear - D2 D6 DP DM1 APd CLO LOQ LM1 P1; cbn [disjoint_from]; repeat split; lia
    | first [ intros X; exfalso; exact (X EI) | intros _; exact HDRl ] ].
Qed.
End SD.
