(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        ASec ASecD AQuar AQuarM F_poison F_flush F_prim_L0 F_sec_A F_sec_B F_sec_C F_quar_A ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma sec_find_in : forall (l : list schunk) (sc : schunk) (p : Z),
  chunks_sep l -> In sc l -> sc_beg sc <= p < sc_beg sc + sc_msize sc -> sec_find l p = Some sc.
Proof.
  induction l as [|c l IH]; intros sc p SEP IN Hp; [destruct IN|]. inversion SEP as [|c' l' AP SEP']; subst.
  cbn [sec_find]. destruct ((sc_beg c <=? p) && (p <? sc_beg c + sc_msize c)) eqn:EC.
  - apply andb_true_iff in EC as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct IN as [->|IN]; [reflexivity|]. exfalso.
    pose proof (proj1 (Forall_forall _ _) AP sc IN) as A. unfold apart_chunks in A. lia.
  - destruct IN as [->|IN]; [| exact (IH sc p SEP' IN Hp)]. exfalso.
    apply andb_false_iff in EC as [E|E]; [apply Z.leb_gt in E| apply Z.ltb_ge in E]; lia.
Qed.

Lemma sc_index_nth : forall (l : list schunk) (sc : schunk),
  chunks_sep l -> Forall (fun c => 0 < sc_msize c) l -> In sc l -> nth_error l (sc_index l sc) = Some sc.
Proof.
  induction l as [|c l IH]; intros sc SEP POS IN; [destruct IN|]. inversion SEP as [|c' l' AP SEP']; subst.
  apply Forall_cons_iff in POS as [PC POS]. cbn [sc_index]. destruct (Z.eqb_spec (sc_beg c) (sc_beg sc)) as [E|NE].
  - destruct IN as [->|IN]; [reflexivity|]. exfalso.
    pose proof (proj1 (Forall_forall _ _) AP sc IN) as A. pose proof (proj1 (Forall_forall _ _) POS sc IN) as PS. cbv beta in PS, PC. unfold apart_chunks in A. lia.
  - destruct IN as [->|IN]; [congruence|]. cbn [nth_error]. exact (IH sc SEP' POS IN).
Qed.

Lemma shvis_unmapped : forall (H : word -> bool) (W : list (Z * Z)) (m m' : mem) (lo hi : Z),
  shvis H m -> munch W m m' ->
  (forall x, in_shadow_band (bv_unsigned x) -> outside W (bv_unsigned x) \/ m' x <> None) ->
  (hi <= 0x7fff8000 \/ 0x10007fff8000 <= lo) ->
  shvis (unhide_range lo hi H) m'.
Proof.
  intros H W m m' lo hi SV MU KEEP OUT x B HX. unfold unhide_range in HX.
  assert (HH : H x = false).
  { apply andb_false_iff in HX as [HX|HX]; [exact HX|]. exfalso. apply negb_false_iff in HX. unfold in_rangeb in HX.
    apply andb_true_iff in HX as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. unfold in_shadow_band in B. lia. }
  destruct (KEEP x B) as [O|N]; [rewrite (MU x O); exact (SV x B HH)| exact N].
Qed.

Lemma shvis_munch_gen : forall (H H' : word -> bool) (W : list (Z * Z)) (m m' : mem),
  shvis H m -> munch W m m' ->
  (forall x, in_shadow_band (bv_unsigned x) -> H' x = false -> H x = false /\ (outside W (bv_unsigned x) \/ m' x <> None)) ->
  shvis H' m'.
Proof.
  intros H H' W m m' SV MU KEEP x B HX. destruct (KEEP x B HX) as [HH [O|N]]; [rewrite (MU x O); exact (SV x B HH)| exact N].
Qed.

Lemma cell_present : forall (mm : mem) (A k : Z) (bs : list byte) (x : word),
  rw_cells asegs mm A [CB (Z.to_nat k) bs] -> 0 <= k -> A <= bv_unsigned x < A + k -> 6328320 <= bv_unsigned x -> mm x <> None.
Proof.
  intros mm A k bs x [_ (_ & _ & WR)] K0 Hx HI. cbn [cells_size csize] in WR. rewrite Nat.add_0_r, Z2Nat.id in WR by exact K0.
  specialize (WR (bv_unsigned x - A) ltac:(lia)). replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in WR by lia.
  rewrite Nodes.wa_unsigned_id in WR. rewrite wview_high in WR by exact HI. exact WR.
Qed.

Definition AREC_SEC_STACK : Z := 624.

Section ARECS.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation PARR := (al_parr AL).

  Definition arec_sec_W (lo q : Z) (S : asec) (sc : schunk) : list (Z * Z) :=
    [(lo, q); (SEC, SEC + 620); (GSTATS_A, GSTATS_A + 16); (THR + 2800, THR + 3168); (PARR, PARR + 2^23);
     (sc_beg sc, sc_beg sc + sc_msize sc); (sh (sc_beg sc), sh (sc_beg sc) + sc_msize sc / 8);
     (sc_beg (sec_last S sc), sc_beg (sec_last S sc) + 32)].

  Definition arec_sec_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (q lo : Z) (P : prim) (S : asec) (sc : schunk) (H : word -> bool) (m : mem) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = sec_dealloc_H sc H
      /\ munch (arec_sec_W lo q S sc) m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ poison_env E m' /\ thread_env L m' /\ shvis H' m'
      /\ RPRIM AL P m' /\ RSEC AL (sec_dealloc S (sc_index (se_chunks S) sc)) m'.

  #[using="Type"] Lemma arec_sec_tail : forall (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
         (m mA : mem) (H : word -> bool) (q lo rz n CBA : Z) (P : prim) (S : asec) (sc : schunk) (stackw : word)
         (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    alayout_ok AL -> shvis H m -> poison_env E m -> thread_env L m ->
    0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - AREC_SEC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    RPRIM AL P m -> RSEC AL S m -> In sc (se_chunks S) ->
    qchunk_wf (mkQC (QSec sc) rz n) -> qchunk_rep AL m (mkQC (QSec sc) rz n) ->
    q <= CBA -> CBA + 16 <= 2^47 ->
    munch [(lo, q); (SEC_MTX, SEC_MTX + 4)] m mA -> wmono asegs m mA -> mem_inv asegs mA -> RSEC AL S mA ->
    stk asegs mA lo (q - 48) -> rw_cells asegs mA (q - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mA CBA [C8 (wz CACHE); C8 stackw] ->
    evt asegs (lzk H (sec_dealloc_tree sc) (arec_sec_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo P S sc H m))
      (MS (mkR xra (wz (q - 48)) gp (wz A0_TP) x5 x6 x7 (wz CBA) (wz (qc_hdr AL (mkQC (QSec sc) rz n))) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (sc_beg sc + 4096)) (wz INSTANCE) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F_ (wz 0x35a1c) fc None mA (seg_rom asegs)).
  Proof.
    intros until x31. intros AO SV PE TE LOH CLO LO QH Q16 RP RS INS CHW CHR CBQ CB47 MU WM MIA RSA ST FR CBC.
    unfold arec_entry, AREC_SEC_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    destruct CHW as (RZ16 & RZM & NR & RZN & _). cbn [qc_rz qc_n qc_kind qc_bsize] in RZ16, RZM, NR, RZN.
    pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & CSEP).
    pose proof (proj1 (Forall_forall _ _) COK sc INS) as CK.
    pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    pose proof CK as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7).
    unfold al_regions in CK7.
    apply Forall_cons_iff in CK7 as [CSP CK7]. apply Forall_cons_iff in CK7 as [CPA CK7].
    apply Forall_cons_iff in CK7 as [CCX CK7]. apply Forall_cons_iff in CK7 as [CTH _].
    cbn [fst snd] in CSP, CPA, CCX, CTH. unfold apart in CSP, CPA, CCX, CTH.
    unfold qc_hdr, qc_blk. cbn [qc_kind qc_rz].
    set (BEG := sc_beg sc) in *. set (MSZ := sc_msize sc) in *.
    set (M := BEG + 4096 + rz - 16) in *.
    assert (N8 : n <= rup8 n < n + 8) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
    assert (MR : BEG + 4096 <= M /\ M + 16 + rup8 n <= BEG + MSZ) by (unfold M; clear - RZ16 RZN; lia).
    assert (EM : M = BEG + 4096 + rz - 16) by reflexivity. clearbody M.
    hide T1. hide T5. hide T6. hide T7. hide SPM. hide Q16. hide RZM. hide CK1. hide EM.

    destruct CHR as ((bits & actx & HDR) & _ & _ & SHL & SHU & SHR & (_ & SHP)).
    unfold qc_hdr, qc_blk in HDR, SHL, SHU, SHR. cbn [qc_kind qc_rz qc_n qc_bsize] in HDR, SHL, SHU, SHR, SHP.
    fold BEG in HDR, SHL, SHU, SHR, SHP. fold MSZ in SHR. unhide EM.
    replace (BEG + 4096 + rz - 16) with M in HDR, SHU, SHR by (clear - EM; lia).
    pose proof RP as (_ & PENV & _ & _ & (ts & TS)).
    assert (GEO : (BEG + MSZ <= 0x7fff8000 \/ 0x10007fff8000 <= BEG) /\ 0x609000 <= BEG /\ BEG + MSZ <= alloc_ceiling /\ 8192 <= MSZ
                  /\ (BEG + MSZ <= THR \/ THR + 4096 <= BEG)) by (clear - CK2 CK5 CK6 CM1 CTH; lia).
    assert (DJA : forall A n0, A + n0 <= lo -> (A + n0 <= SEC_MTX \/ SEC_MTX + 4 <= A) -> disjoint_from [(lo, q); (SEC_MTX, SEC_MTX + 4)] A n0)
      by (intros A n0 D1 D2; cbn [disjoint_from]; clear - D1 D2 LO; lia).
    eapply (rw_cells_transport asegs _ m mA) in HDR; [| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJA; clear - GEO MR N8 NR CLO; lia].
    eapply (rw_cells_transport asegs _ m mA) in TS; [| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJA; clear - T3 T4 CLO; lia].
    assert (PEA : poison_env E mA).
    { eapply poison_env_frame2; [exact PE| exact MU| exact WM|]. unfold sec_clear. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LO CLO ACR; lia. }
    assert (TEA : thread_env L mA).
    { eapply thread_env_frame2; [exact TE| exact MU| exact WM|]. unhide T1. unhide T5. unfold thread_clear2.
      repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - T1 T2 T3 T4 T5 LO CLO ACR; repeat split; lia. }
    assert (SVA : shvis H mA) by (eapply shvis_wmono; [exact SV| exact WM]).
    assert (RPA : RPRIM AL P mA).
    { apply (RPRIM_frame_m AL AO P _ m mA RP MU). unfold prim_clear.
      assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
      assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
      repeat (apply Forall_cons || apply Forall_nil); left; unfold prim_out; cbn [fst snd]; clear - LO CLO LOH ACR T3 T4 SP1 SP2 SHS SHS0; repeat split; lia. }
    clear PENV.

    zstep.
    unhide Q16.
    eapply evt_cut.
    { eapply (gcts_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc (q - 48) mA lo).
      - exact ST.
      - exact CLO.
      - clear - LO; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact TEA.
      - exact TLO.
      - exact MIA. }
    hide Q16.
    cbv beta. unfold gcts_post. intros msG (g1 & mG & -> & MUg & WMg & MIG & STG & TEG).

    assert (DJG : forall A n0, (A + n0 <= q - 48 - 32 \/ q - 48 <= A) -> disjoint_from [(q - 48 - 32, q - 48)] A n0)
      by (intros A n0 D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mA mG) in HDR; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear - GEO MR N8 NR CLO LO; lia].
    eapply (rw_cells_transport asegs _ mA mG) in FR; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear; lia].
    eapply (rw_cells_transport asegs _ mA mG) in CBC; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear - CBQ; lia].
    eapply (rw_cells_transport asegs _ mA mG) in TS; [| exact MUg| exact WMg| cbn [cells_size csize Nat.add]; apply DJG; clear - T4 CLO LO; lia].
    replace (ret_pc (Z_to_bv 64 219680)) with (Z_to_bv 64 219680) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    pose proof (rw_cells_split_CB asegs mG (THR + 2800) [] _ ts [] [40%nat; 8%nat; 8%nat; 312%nat] TS ltac:(reflexivity)) as TSS.
    cbn [mk_CB_cells app] in TSS. clear TS.
    remember (firstn 40 ts) as tsa eqn:Etsa. remember (skipn 40 ts) as ts1 eqn:Ets1. clear Etsa Ets1.
    remember (firstn 8 ts1) as tb1 eqn:E1. remember (skipn 8 ts1) as ts2 eqn:E2. clear E1 E2.
    remember (firstn 8 ts2) as tb2 eqn:E1. remember (skipn 8 ts2) as ts3 eqn:E2. clear E1 E2.
    remember (firstn 312 ts3) as tsb eqn:E1. clear E1.
    apply (rw_cells_CB_C8 asegs mG (THR + 2800) [CB 40 tsa] tb1) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs mG (THR + 2800) [CB 40 tsa; C8 (le_bytes_to_word tb1)] tb2) in TSS. cbn [app] in TSS.

    assert (HS : rw_cells asegs mG M [CB 2 [Z_to_bv 8 3; bits]; C2 (wz 0); C4 (wz n); C8 actx]).
    { eapply rw_cells_rebytes; [exact HDR| | | ].
      - cbn [cells_wf cell_wf]. repeat split.
      - cbn [cells_bytes cbytes app]. change (le2 (Z_to_bv 64 0)) with [Z_to_bv 8 0; Z_to_bv 8 0]. reflexivity.
      - reflexivity. }
    clear HDR.
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (unfold zx32; rewrite unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep.
    zstep.
    do 4 zstep.

    hide HS. hide FR. hide CBC. hide MU. hide WM. hide MUg. hide WMg.
    pose proof (munch_refl [(THR + 2800, THR + 3168)] mG) as MUs. pose proof (wmono_refl asegs mG) as WMs.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
    unhide HS. unhide FR. unhide CBC. unhide MU. unhide WM. unhide MUg. unhide WMg.
    assert (DJS : forall A n0, (A + n0 <= THR + 2800 \/ THR + 3168 <= A) -> disjoint_from [(THR + 2800, THR + 3168)] A n0)
      by (intros A n0 D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mG mT) in HS; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add]; apply DJS; clear - GEO MR N8 NR; lia].
    eapply (rw_cells_transport asegs _ mG mT) in FR; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add]; apply DJS; clear - T4 CLO LO; lia].
    eapply (rw_cells_transport asegs _ mG mT) in CBC; [| exact MUs| exact WMs| cbn [cells_size csize Nat.add]; apply DJS; clear - CBQ T4 CLO LO; lia].

    assert (MUT : munch [(q - 80, q - 48); (THR + 2800, THR + 3168)] mA mT).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUg]| eapply munch_weaken; [| exact MUs]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [intros R; apply O1; clear - R; lia| exact I].
      - split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WMg WMs) as WMT.
    clear MUg WMg MUs WMs.
    zstep. if_cases KP; zify_cond KP. { exfalso. clear - KP GEO. lia. } clear KP.

    assert (RPT : RPRIM AL P mT).
    { apply (RPRIM_frame_ts AL AO P _ mA mT RPA MUT).
      - unfold prim_clear_ts.
        assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
        assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
        apply Forall_cons; [left; unfold prim_out; cbn [fst snd]; clear - LO CLO LOH ACR T3 T4 SP1 SP2 SHS SHS0; repeat split; lia|].
        apply Forall_cons; [right; right; cbn [fst snd]; clear; lia| apply Forall_nil].
      - destruct (rw_cells_forget _ _ _ _ TSS) as [ts' X]. exists ts'. exact X. }
    pose proof RPT as (_ & PENVT & _).
    pose proof PENVT as PENVC. unfold prim_env in PENVC.
    zstep.

    assert (JOIN : forall v11 v13 v14 v20 : word,
      evt asegs (lzk H (sec_dealloc_tree sc) (arec_sec_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo P S sc H m))
        (MS (mkR (wz 219680) (wz (q - 48)) gp (wz A0_TP) x5 x6 x7 (wz CBA) (wz M) (wz (THR + 2800)) v11 (wz n) v13 v14 x15 x16 x17
                 (wz (BEG + 4096)) (wz 721560) v20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F_ (wz 0x35ab8) fc None mT (seg_rom asegs))); [|
      zstep; if_cases K5; zify_cond K5;
      [ apply JOIN
      | zstep; zstep; if_cases K6; zify_cond K6; [ apply JOIN | exfalso; clear - K5 K6 CSP GEO SP1; lia ] ] ].
    intros v11 v13 v14 v20.

    do 3 zstep.
    do 6 zstep.
    zstep. replace (q - 48 + 48) with q by lia.
    zstep.
    release_frame FR STG q.

    unhide CK1. unhide RZM. demod CK1 bz. demod RZM rzz. demod CM2 mz.
    assert (R8 : exists r8, rup8 n = 8 * r8) by (unfold rup8; eexists; rewrite Z.mul_comm; reflexivity). destruct R8 as [r8 R8].
    assert (SG : sh (BEG + 4096) = sh BEG + 512 /\ sh (M + 16) = sh BEG + 512 + 2 * rzz /\ sh (M + 16 + rup8 n) = sh BEG + 512 + 2 * rzz + r8
                 /\ rz / 8 = 2 * rzz /\ rup8 n / 8 = r8 /\ (MSZ - 4096 - rz - rup8 n) / 8 = 512 * mz - 512 - 2 * rzz - r8 /\ MSZ / 8 = 512 * mz
                 /\ 0 <= rzz /\ 0 <= r8 /\ 0 <= 512 * mz - 512 - 2 * rzz - r8
                 /\ 2147450880 <= sh BEG /\ sh BEG + 512 * mz <= 17594333495296).
    { unfold sh, SHADOW_OFF. rewrite R8 in *. clear - CK1 RZM CM2 EM RZ16 RZN N8 NR CK2 CK6 ACR. Z.div_mod_to_equations. lia. }
    destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9 & SG10 & SG11 & SG12).
    rewrite SG1 in SHL. rewrite SG2 in SHU. rewrite SG3 in SHR. rewrite SG4 in SHL. rewrite SG5 in SHU. rewrite SG6 in SHR.
    assert (DJB : forall A n0, 2147450880 <= A -> A + n0 <= 17594333495296 ->
                  disjoint_from [(lo, q); (722240, 722240 + 4)] A n0 /\ disjoint_from [(q - 80, q - 48); (THR + 2800, THR + 3168)] A n0).
    { intros A n0 D1 D2. cbn [disjoint_from]. clear - D1 D2 LO LOH T3 T4. lia. }
    assert (TR : forall A k (bs : list byte), rw_cells asegs m A [CB (Z.to_nat k) bs] -> 0 <= k -> 2147450880 <= A -> A + k <= 17594333495296 ->
                 rw_cells asegs mT A [CB (Z.to_nat k) bs]).
    { intros A k bs X K0 D1 D2. destruct (DJB A k D1 D2) as [J1 J2].
      eapply (rw_cells_transport asegs _ mA mT); [| exact MUT| exact WMT| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by exact K0; exact J2].
      eapply (rw_cells_transport asegs _ m mA); [exact X| exact MU| exact WM| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by exact K0; exact J1]. }
    apply (TR _ 512) in SHP; [| clear; lia| clear - SG11; lia| clear - SG10 SG8 SG9 SG12; lia].
    apply TR in SHL; [| clear - SG8; lia| clear - SG11; lia| clear - SG10 SG8 SG9 SG12; lia].
    apply TR in SHU; [| exact SG9| clear - SG11 SG8; lia| clear - SG10 SG8 SG9 SG12; lia].
    apply TR in SHR; [| exact SG10| clear - SG11 SG8 SG9; lia| clear - SG10 SG8 SG9 SG12; lia].
    clear TR DJB.
    pose proof (cb_join mT (sh BEG) _ _ _ _ SHP ltac:(rewrite Z2Nat.id by (clear; lia); exact SHL)) as J1.
    pose proof (cb_join mT (sh BEG) _ _ _ _ J1 ltac:(rewrite Nat2Z.inj_add, !Z2Nat.id by (clear - SG8; lia); replace (sh BEG + (512 + 2 * rzz)) with (sh BEG + 512 + 2 * rzz) by (clear; lia); exact SHU)) as J2.
    pose proof (cb_join mT (sh BEG) _ _ _ _ J2 ltac:(rewrite !Nat2Z.inj_add, !Z2Nat.id by (clear - SG8 SG9; lia); replace (sh BEG + (512 + 2 * rzz + r8)) with (sh BEG + 512 + 2 * rzz + r8) by (clear; lia); exact SHR)) as J3.
    replace (Z.to_nat 512 + Z.to_nat (2 * rzz) + Z.to_nat r8 + Z.to_nat (512 * mz - 512 - 2 * rzz - r8))%nat with (Z.to_nat (MSZ / 8)) in J3
      by (rewrite SG7; clear - SG8 SG9 SG10; lia).
    clear J1 J2 SHP SHL SHU SHR.

    assert (PET : poison_env E mT).
    { eapply poison_env_frame2; [exact PEA| exact MUT| exact WMT|]. unfold sec_clear. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LO CLO ACR T3 T4; lia. }
    assert (TET : thread_env L mT).
    { eapply thread_env_frame2; [exact TEA| exact MUT| exact WMT|]. unhide T1. unhide T5. unfold thread_clear2.
      repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - T1 T2 T3 T4 T5 LO CLO ACR; repeat split; lia. }
    assert (SVT : shvis H mT) by (eapply shvis_wmono; [exact SVA| exact WMT]).
    assert (RST : RSEC AL S mT).
    { eapply (RSEC_frame_but AL S _ mA mT RSA MUT (wmono_but_of_wmono _ _ _ WMT)).
      - repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LO CLO ACR T3 T4; lia.
      - layout_facts AO 1%nat LPARR. clear - LPARR. lia.
      - layout_facts AO 1%nat LPARR. layout_apart_fact AO 1%nat 3%nat LP13. cbn [disjoint_from]. clear - LPARR LP13 LO CLO ACR T3 T4. lia.
      - apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & D2 & _ & _ & D5 & D6 & D7).
        unfold al_regions in D7. apply Forall_cons_iff in D7 as [_ D7]. apply Forall_cons_iff in D7 as [_ D7].
        apply Forall_cons_iff in D7 as [_ D7]. apply Forall_cons_iff in D7 as [DT _]. cbn [fst snd] in DT. unfold apart in DT.
        pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _].
        cbn [disjoint_from]. clear - DT DM D6 LO CLO. lia. }

    destruct (rw_cells_forget _ _ _ _ TSS) as [ts' TST]. cbn [cells_size csize Nat.add] in TST.
    assert (POSM : Forall (fun d => 0 < sc_msize d) (se_chunks S)).
    { apply Forall_forall. intros d Hd. pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _]. clear - DM. lia. }
    pose proof (sc_index_nth (se_chunks S) sc CSEP POSM INS) as NTH.
    unhide Q16.
    lz_here.
    eapply implA_mono.
    { eapply (sec_dealloc_spec E AL ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo mT H S (sc_index (se_chunks S) sc) sc _ _ _ _ _ _ _ _ _ _ _ _ ts' _).
      - exact MIG.
      - assumption.
      - exact PET.
      - exact TET.
      - exact TLO.
      - exact AO.
      - exact RST.
      - exact NTH.
      - exact TST.
      - exact J3.
      - exact STG.
      - exact CLO.
      - exact LO.
      - exact Q16.
      - exact QH. }
    intros a H' ms' PO. unfold sec_dealloc_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & -> & MUd & WBd & MId & STd & PEd & TEd & RSd & (tsd & TSd) & FEd).

    set (lastc := sec_last S sc) in *.
    assert (INL : In lastc (se_chunks S)).
    { unfold lastc, sec_last. apply nth_In. destruct (se_chunks S) as [|x l]; [destruct INS| cbn [length]; clear; lia]. }
    pose proof (proj1 (Forall_forall _ _) COK lastc INL) as (_ & L2 & _ & _ & L5 & L6 & L7).
    pose proof (chunk_ok_msize AL lastc (proj1 (Forall_forall _ _) COK lastc INL)) as [LM _].
    unfold al_regions in L7. apply Forall_cons_iff in L7 as [LSP L7]. apply Forall_cons_iff in L7 as [_ L7].
    apply Forall_cons_iff in L7 as [_ L7]. apply Forall_cons_iff in L7 as [LTH _]. cbn [fst snd] in LSP, LTH. unfold apart in LSP, LTH.
    layout_facts AO 1%nat LPARR. layout_apart_fact AO 0%nat 1%nat LP01. layout_apart_fact AO 1%nat 3%nat LP13.
    assert (SHS0 : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (SHM : (BEG + MSZ <= al_space AL -> sh BEG + 512 * mz <= sh (al_space AL))
                  /\ (al_space AL + K_SPACE + 4096 <= BEG -> sh (al_space AL + K_SPACE + 4096) <= sh BEG)).
    { unfold sh, SHADOW_OFF. clear - CM2 CK1 SP1. split; intros X; Z.div_mod_to_equations; lia. }
    destruct SHM as [SHM1 SHM2].
    unfold arec_sec_post. exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    {
      unfold arec_sec_W. fold BEG. fold MSZ. fold lastc.
      eapply munch_trans; [eapply munch_weaken; [| exact MU]|].
      { unfold sub_fp. cbn [outside]. intros xo (O1 & O2 & _). split; [intros R; apply O1; clear - R LO; lia|]. split; [intros R; apply O2; clear - R; lia| exact I]. }
      eapply munch_trans; [eapply munch_weaken; [| exact MUT]| eapply munch_weaken; [| exact MUd]].
      - unfold sub_fp. cbn [outside]. intros xo (O1 & _ & _ & O4 & _). split; [intros R; apply O1; clear - R LO; lia|]. split; [exact O4| exact I].
      - unfold sub_fp. cbn [outside]. intros xo (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & _).
        split; [intros R; apply O1; clear - R LO; lia|]. repeat (split; [assumption|]). exact I. }
    split; [exact MId|]. split; [exact STd|]. split; [exact PEd|]. split; [exact TEd|].

    split.
    {
      eapply (shvis_munch_gen H _ _ mT m' SVT MUd).
      intros x B HX. unfold in_shadow_band in B.
      assert (B' : 2147450880 <= bv_unsigned x < 17594333495296) by (clear - B; lia). clear B.
      assert (HF : flush_H BEG MSZ H x = false).
      { unfold sec_dealloc_H in HX. change (poison_H (sc_beg sc) (sc_msize sc) 0 H) with H in HX. fold BEG MSZ in HX.
        unfold unhide_range in HX. apply andb_false_iff in HX as [HX|HX]; [exact HX|]. exfalso.
        apply negb_false_iff in HX. unfold in_rangeb in HX. apply andb_prop in HX as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        clear - X1 X2 B' CK5. lia. }
      clear HX.
      assert (OUTW : bv_unsigned x < sh BEG \/ sh BEG + 512 * mz <= bv_unsigned x ->
                     outside [(q - 624, q); (721624, 721624 + 620); (722264, 722264 + 16); (THR + 2800, THR + 3168); (PARR, PARR + 2 ^ 23);
                              (BEG, BEG + MSZ); (sh BEG, sh BEG + MSZ / 8); (sc_beg lastc, sc_beg lastc + 32)] (bv_unsigned x)).
      { intros X. rewrite SG7. cbn [outside]. clear - B' X LO LOH T3 T4 LPARR CK5 CK2 L5 L2 LM. repeat split; intros R; lia. }
      unfold flush_H, flush_edges, flush_range in HF, FEd. fold BEG in HF, FEd. fold MSZ in HF, FEd. rewrite SG7 in FEd.
      assert (SHE : sh (BEG + MSZ) = sh BEG + 512 * mz) by (unfold sh; clear - CK1 CM2; Z.div_mod_to_equations; lia).
      pose proof (fl_pgup_ge (sh BEG)) as G1. pose proof (fl_pgdn_le (sh (BEG + MSZ))) as G2. rewrite SHE in G2 at 2.
      set (pb := pgup (sh BEG)) in *. set (pe := pgdn (sh (BEG + MSZ))) in *.
      destruct (pe <=? pb) eqn:EF.
      - split; [exact HF|].
        destruct (Z_lt_ge_dec (bv_unsigned x) (sh BEG)) as [X1|X1]; [left; apply OUTW; left; exact X1|].
        destruct (Z_lt_ge_dec (bv_unsigned x) (sh BEG + 512 * mz)) as [X2|X2]; [| left; apply OUTW; right; clear - X2; lia].
        right. apply (cell_present m' (sh BEG) (512 * mz) _ x FEd); [clear - SG8 SG9 SG10; lia| clear - X1 X2; lia| clear - B'; lia].
      - apply Z.leb_gt in EF. destruct FEd as [FE1 FE3]. replace (pb + (pe - pb)) with pe in HF, FE3 by (clear; lia).
        unfold hide_range in HF. apply orb_false_iff in HF as [HF1 HF2]. split; [exact HF1|].
        unfold in_rangeb in HF2.
        destruct (Z_lt_ge_dec (bv_unsigned x) (sh BEG)) as [X1|X1]; [left; apply OUTW; left; exact X1|].
        destruct (Z_lt_ge_dec (bv_unsigned x) (sh BEG + 512 * mz)) as [X2|X2]; [| left; apply OUTW; right; clear - X2; lia].
        right. destruct (Z_lt_ge_dec (bv_unsigned x) pb) as [X3|X3].
        + apply (cell_present m' (sh BEG) (pb - sh BEG) _ x FE1); [clear - G1; lia| clear - X1 X3; lia| clear - B'; lia].
        + assert (X4 : pe <= bv_unsigned x).
          { apply andb_false_iff in HF2 as [W|W]; [apply Z.leb_gt in W; clear - W X3; lia| apply Z.ltb_ge in W; exact W]. }
          apply (cell_present m' pe (sh BEG + 512 * mz - pe) _ x FE3); [clear - G2; lia| clear - X4 X2; lia| clear - B'; lia]. }

    split; [| exact RSd].

    apply (RPRIM_frame_ts AL AO P _ mT m' RPT MUd); [| exists tsd; exact TSd].
    unfold prim_clear_ts. fold BEG. fold MSZ. fold lastc. rewrite SG7.
    assert (POL : forall xa xb, xb <= 17594333495296 -> (xb <= 2147450880 \/ (xa <= xb /\ 2147450880 <= xa /\ (xb <= sh (al_space AL) \/ sh (al_space AL + K_SPACE + 4096) <= xa))) ->
                 (xb <= THR + CACHE_OFF \/ THR + TSTATS_OFF + 368 <= xa) -> (xb <= 721592 \/ 721592 + 25 <= xa) -> prim_out AL (xa, xb)).
    { intros xa xb B1 B2 B3 B4. unfold prim_out. cbn [fst snd]. clear - B1 B2 B3 B4 SP1 SHS0. repeat split; lia. }
    assert (POH : forall xa xb, (xb <= al_space AL \/ al_space AL + K_SPACE + 4096 <= xa) -> 17594333495296 <= xa ->
                 (xb <= THR + CACHE_OFF \/ THR + TSTATS_OFF + 368 <= xa) -> prim_out AL (xa, xb)).
    { intros xa xb B1 B2 B3. unfold prim_out. cbn [fst snd]. clear - B1 B2 B3 SHS. repeat split; lia. }
    apply Forall_cons. { left. apply POH; clear - LO CLO LOH ACR SP2 T4; lia. }
    apply Forall_cons. { left. apply POL; [clear; lia| left; clear; lia| clear - T3; lia| clear; lia]. }
    apply Forall_cons. { left. apply POL; [clear; lia| left; clear; lia| clear - T3; lia| clear; lia]. }
    apply Forall_cons. { right. right. cbn [fst snd]. clear. lia. }
    apply Forall_cons.
    { left. destruct LPARR as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      destruct (Z_le_gt_dec 17594333495296 PARR) as [HP|HP]; [apply POH; clear - HP LP01 LP13 T3; lia|].
      apply POL; [clear - HP P1; lia| left; clear - HP P1; lia| clear - LP13; lia| clear - HP P1; lia]. }
    apply Forall_cons.
    { left. destruct (Z_le_gt_dec 17594333495296 BEG) as [HP|HP]; [apply POH; clear - HP CSP CTH; lia|].
      apply POL; [clear - HP CK5; lia| left; clear - HP CK5; lia| clear - CTH; lia| clear - CK2; lia]. }
    apply Forall_cons.
    { left. apply POL; [clear - SG12; lia| right; clear - SG8 SG9 SG10 SG11 SHM1 SHM2 CSP; lia| clear - SG11 SG12 T3 T4; lia| clear - SG11; lia]. }
    apply Forall_cons; [| apply Forall_nil].
    { left. destruct (Z_le_gt_dec 17594333495296 (sc_beg lastc)) as [HP|HP]; [apply POH; clear - HP LSP LTH LM; lia|].
      apply POL; [clear - HP L5 LM; lia| left; clear - HP L5 LM; lia| clear - LTH LM; lia| clear - L2; lia]. }

  Qed.

  #[using="Type"] Theorem arec_sec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32)
         (m : mem) (H : word -> bool) (q lo rz n CBA : Z) (P : prim) (S : asec) (sc : schunk) (stackw : word),
    alayout_ok AL -> mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> thread_env L m ->
    stk asegs m lo q -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - AREC_SEC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
    RPRIM AL P m -> RSEC AL S m -> In sc (se_chunks S) ->
    qchunk_wf (mkQC (QSec sc) rz n) -> qchunk_rep AL m (mkQC (QSec sc) rz n) ->
    rw_cells asegs m CBA [C8 (wz CACHE); C8 stackw] -> q <= CBA -> CBA + 16 <= 2^47 ->
    implA H (sec_dealloc_tree sc)
          (arec_sec_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo P S sc H m)
          (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz CBA) (wz (qc_hdr AL (mkQC (QSec sc) rz n))) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F_ (wz arec_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m H q lo rz n CBA P S sc stackw
           AO MI MC SV PE TE ST LOH CLO LO QH Q16 RP RS INS CHW CHR CBC CBQ CB47.
    unfold arec_entry, AREC_SEC_STACK in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat LP03.
    pose proof CHW as CHW0. destruct CHW as (RZ16 & RZM & NR & RZN & _). cbn [qc_rz qc_n qc_kind qc_bsize] in RZ16, RZM, NR, RZN.
    pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & CSEP).
    pose proof (proj1 (Forall_forall _ _) COK sc INS) as CK.
    pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    pose proof CK as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & CK7).
    unfold al_regions in CK7.
    apply Forall_cons_iff in CK7 as [CSP CK7]. apply Forall_cons_iff in CK7 as [CPA CK7].
    apply Forall_cons_iff in CK7 as [CCX CK7]. apply Forall_cons_iff in CK7 as [CTH _].
    cbn [fst snd] in CSP, CPA, CCX, CTH. unfold apart in CSP, CPA, CCX, CTH.
    unfold qc_hdr, qc_blk. cbn [qc_kind qc_rz].
    set (BEG := sc_beg sc) in *. set (MSZ := sc_msize sc) in *.
    set (M := BEG + 4096 + rz - 16) in *.
    assert (N8 : n <= rup8 n < n + 8) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
    assert (MR : BEG + 4096 <= M /\ M + 16 + rup8 n <= BEG + MSZ) by (unfold M; clear - RZ16 RZN; lia).
    assert (EM : M = BEG + 4096 + rz - 16) by reflexivity. clearbody M.
    hide T1. hide T5. hide T6. hide T7. hide SPM. hide Q16. hide RZM. hide CK1. hide EM.
    pose proof (munch_refl [(q - 48, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 48%nat ST.
    do 6 zstep.
    do 4 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -48) with (q - 48) in * by lia.

    pose proof RP as (_ & PENV & _).
    assert (PENVA : prim_env AL mA).
    { eapply prim_env_frame; [exact PENV| exact MU| exact WM|]. clear - LO CLO ACR SP1 SP2. env_clear. }
    pose proof PENVA as PENVC. unfold prim_env in PENVC.
    zstep.
    do 2 zstep.
    clear PENVC.

    assert (JOIN : forall v10 v11 : word,
      evt asegs (lzk H (sec_dealloc_tree sc) (arec_sec_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc q lo P S sc H m))
        (MS (mkR ra (wz (q - 48)) gp (wz A0_TP) t0 t1 t2 (wz CBA) (wz M) v10 v11 a2 a3 a4 a5 a6 a7
                 s2 (wz 721560) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F_ (wz 0x3591c) fc None mA (seg_rom asegs))); [|
      zstep; if_cases K1; zify_cond K1;
      [ apply JOIN
      | zstep; zstep; if_cases K2; zify_cond K2; [ apply JOIN | exfalso; clear - K1 K2 CSP MR CM1 SP1 N8 NR; lia ] ] ].
    intros v10 v11.
    assert (RSA : RSEC AL S mA).
    { eapply (RSEC_frame_but AL S _ m mA RS MU (wmono_but_of_wmono _ _ _ WM)).
      - repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear - LO CLO ACR; lia.
      - layout_facts AO 1%nat LPARR. clear - LPARR. lia.
      - layout_facts AO 1%nat LPARR. cbn [disjoint_from]. clear - LPARR LO CLO ACR. lia.
      - apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & _ & _ & _ & _ & D6 & _).
        pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _].
        cbn [disjoint_from]. clear - DM D6 LO CLO. lia. }
    do 2 zstep.
    zstep.
    eapply evt_cut.
    { eapply (gbb_spec AL) with (m := mA) (q := q - 48) (lo := lo) (p := M) (S := S).
      - exact MI.
      - exact AO.
      - exact RSA.
      - exact ST.
      - exact CLO.
      - clear - LO; lia.
      - clear - QH; lia.
      - reflexivity.
      - reflexivity.
      - clear - MR CK2 CK6 ACR CM1 N8 NR; lia. }
    cbv beta. unfold gbb_post. intros msB (y5 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & mB & -> & MUb & WMb & MIB & STB & RSB).

    assert (EBB : sec_block_begin S M = BEG + 4096).
    { unfold sec_block_begin. rewrite (sec_find_in (se_chunks S) sc M CSEP INS ltac:(fold BEG; fold MSZ; clear - MR N8 NR; lia)). reflexivity. }
    rewrite EBB. clear EBB.
    replace (ret_pc (Z_to_bv 64 219432)) with (Z_to_bv 64 219432) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (DJB : forall A n0, (A + n0 <= q - 80 \/ q - 48 <= A) -> (A + n0 <= SEC_MTX \/ SEC_MTX + 4 <= A) -> disjoint_from [(q - 48 - 32, q - 48); (SEC_MTX, SEC_MTX + 4)] A n0)
      by (intros A n0 D1 D2; cbn [disjoint_from]; clear - D1 D2; lia).
    eapply (rw_cells_transport asegs _ mA mB) in FR; [| exact MUb| exact WMb| cbn [cells_size csize Nat.add]; apply DJB; clear - LO CLO ACR; lia].
    eapply (rw_cells_transport asegs _ mA mB) in CBC; [| exact MUb| exact WMb| cbn [cells_size csize Nat.add]; apply DJB; clear - CBQ LO CLO ACR; lia].
    assert (PENVB : prim_env AL mB).
    { unfold prim_env in *. eapply (rw_cells_transport asegs _ mA mB); [exact PENVA| exact MUb| exact WMb|]. cbn [cells_size csize Nat.add]. apply DJB; clear - LO CLO ACR; lia. }
    pose proof PENVB as PENVC. unfold prim_env in PENVC.
    assert (MUB : munch [(lo, q); (SEC_MTX, SEC_MTX + 4)] m mB).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUb]]; unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [intros R; apply O1; clear - R LO; lia| exact I].
      - split; [intros R; apply O1; clear - R LO; lia|]. split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM WMb) as WMB.
    zstep.
    zstep.
    zstep.
    clear PENVC.
    unhide Q16.
    assert (EMQ : M = qc_hdr AL (mkQC (QSec sc) rz n)) by (unhide EM; rewrite EM; reflexivity).
    zstep. if_cases K3; zify_cond K3.
    -
      zstep. if_cases K4; zify_cond K4. 2: { exfalso. clear - K3 K4 CSP CM1 SP1. lia. }
      rewrite EMQ. eapply (arec_sec_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m mB H q lo rz n CBA P S sc stackw); eassumption.
    - zstep.
      rewrite EMQ. eapply (arec_sec_tail ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m mB H q lo rz n CBA P S sc stackw); eassumption.

  Qed.
End ARECS.

