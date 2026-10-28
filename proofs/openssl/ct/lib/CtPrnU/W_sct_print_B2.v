(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApBase ApState CtSizes CtWire CtTime CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_prefix_create W_obj_free W_obj_lookup W_asn1_string W_bio_push W_bio_write W_bio_printf W_snprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv PrnKit PrnHeapLo PrnLeaf PrnFmt PrnTimeIface W_bio_hex_string W_sct_print_nv1 W_sct_print_A W_sct_print_B1 W_sct_print_B3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Local Ltac xport H MU WM :=
  lazymatch type of MU with munch ?W ?ma ?mb => apply (rw_cells_transport ctusegs W ma mb) in H; [| exact MU| exact WM|] end.


Section SPB. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp : word) (m1 : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word).
Variables (K KS : list block) (pbio : bptr) (out pv ts TSTK : Z).

Hypothesis LOB : lo <= bv_unsigned sp - 96 - Z.max 8320 TSTK.
Hypothesis SPB63 : bv_unsigned sp <= B /\ B < 2^63.
Hypothesis HBIN : In (pbio, out, BIO_SIZE) OW.
Hypothesis NI : ~ In pbio (es_ids st ++ env_ids E).
Hypothesis HK : frozen (forall b, In b K -> In b (OW ++ LB) /\ blk_id b <> pbio).
Hypothesis HKS : frozen (forall b, In b KS -> In b (OW ++ LB) /\ blk_id b <> pbio).
Hypothesis TSW : 0 <= ts < 2^64.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis T_ADJ_OK : gentime_adj_ok_stmt TSTK.
Hypothesis T_SETSTR_OK : gentime_setstr_ok_stmt TSTK.
Hypothesis T_PRINT : gentime_print_stmt TSTK.

Local Notation pb_invN := (pb_inv sp m1 s st OW LB E bo lo B canary K KS out pv).
Local Notation pb_step_munchN := (pb_step_munch sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).
Local Notation pb_step_nodeN := (pb_step_node sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).
Local Notation pb_openN := (pb_open sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).
Local Notation pb_blocksN := (pb_blocks sp m1 s st OW LB E bo lo B canary K KS pbio out pv ts TSTK LOB SPB63 HBIN NI HK HKS TSW).

(* [comment removed for export] *)
Lemma nb_bio_disjoint : forall sC L mC (q : bptr) A n,
  RHEAP sC L mC -> In (q, A, n) L -> In (pbio, out, BIO_SIZE) L -> q <> pbio -> A + n <= out \/ out + BIO_SIZE <= A.
Proof. intros sC L mC q A n HEAP H1 H2 NE. exact (blk_disjoint _ _ _ _ _ _ _ _ _ HEAP H1 H2 NE). Qed.

(* [comment removed for export] *)
Lemma seg_B_ok : forall {X : Type} (x1 t0 t1 t2 a4 a5 a6 a7 x18 x19 x20 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (s2 : PState) (m2 : mem) (errv2 : word) (clo : list cell) (nw : Z) (g : bptr) (G : Z) (t : tm6)
    (k2 : option bptr -> lprog X) (k3 : bptr -> option bptr -> lprog X) (k4 : lprog X) (Q : X -> PState -> machine_state -> Prop),
  pb_invN s2 m2 [(g, G, 24)] errv2 clo nw -> frm0 fc -> rblock_range G 24 ->
  rw_cells ctusegs m2 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
  gentime_adj ts = Some t ->
  k2 None = LUnr -> (forall dp, k2 (Some dp) = LReallocI dp 19 (k3 dp)) -> (forall dp, k3 dp None = LUnr) ->
  (forall dp dp', k3 dp (Some dp') = LFree dp' (LFree g k4)) ->
  (forall (s3 : PState) (m3 : mem) (errv3 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (clo' : list cell) (nw' : Z),
     pb_invN s3 m3 [] errv3 clo' nw' -> frm0 fc' -> sp_F Fc Fc' ->
     implM ctusegs (interp k4) s3 Q
       (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0' t1' t2' sp (Z_to_bv 64 out) a0' a1' a2' a3' a4' a5' a6' a7'
                x18 x19 x20 x21' (Z_to_bv 64 ts) x23 x24 x25 x26 x27 t3' t4' t5' t6')
           Fc' (Z_to_bv 64 SCT_PRINT_TAIL) fc' None m3 (seg_rom ctusegs))) ->
  implM ctusegs (interp (LMalloc 20 k2)) s2 Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 out)
             (Z_to_bv 64 G) (Z_to_bv 64 0) (Z_to_bv 64 (ts_day ts)) (Z_to_bv 64 (ts_sec ts)) a4 a5 a6 a7
             x18 x19 x20 (Z_to_bv 64 G) (Z_to_bv 64 ts) x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_PRINT_ADJ) fc None m2 (seg_rom ctusegs)).
Proof using HBIN HF HK HKS LOB NI SP16 SPB63 TSW T_ADJ_OK T_PRINT T_SETSTR_OK.
  intros until Q. intros INV FRM BRG HG ADJ K2N K2S K3N K3S KONT.
  pose proof (pb_blocksN _ _ _ _ _ _ INV) as (OB0 & OB1 & OB2 & KSB & CEIL & GLO). unfold GLOBALS_TOP in GLO.
  pose proof (pb_openN _ _ _ _ _ _ INV) as (HEAP & AS & AUX & QB & B63 & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & SZ & NW & HB).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof BRG as (G0 & G16 & _ & GC & GI).
  assert (PRT : printable ts = true) by (unfold printable; rewrite ADJ; reflexivity).
  pose proof (LH_nodup _ _ _ HEAP) as ND2. cbn [map blk_id fst snd app] in ND2.
  assert (NIg : ~ In g (map blk_id (OW ++ LB))) by (apply NoDup_cons_iff in ND2; exact (proj1 ND2)).
  assert (NEg : g <> pbio) by (intros ->; apply NIg; rewrite map_app; apply in_app_iff; left; apply in_map_iff; exists (pbio, out, BIO_SIZE); split; [reflexivity| exact HBIN]).
  assert (HBL : forall NB, In (pbio, out, BIO_SIZE) (NB ++ OW ++ LB)) by (intros NB; apply in_app_iff; right; apply in_app_iff; left; exact HBIN).
  pose proof (nb_bio_disjoint _ _ _ g G 24 HEAP ltac:(left; reflexivity) (HBL [(g, G, 24)]) NEg) as DJG. unfold BIO_SIZE in DJG.
  assert (O16 : out mod 16 = 0) by (pose proof (blk_bounds _ _ _ _ _ _ HEAP (HBL [(g, G, 24)])) as (_ & _ & _ & _ & O16); exact O16).
  unfold SCT_PRINT_ADJ, MallocRep.wz.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  zstep. ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
  eapply (T_ADJ_OK X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m2 s2 ([(g, G, 24)] ++ OW ++ LB) lo B errv2 canary G g ts t k2 Q);
    [exact HEAP| exact AUX| rewrite ESP; lia| rewrite ESP; lia| rewrite ESP; exact ST| exact CEIL| unfold GLOBALS_TOP; lia| rewrite ESP; lia
    | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia
    | exact ERR| exact MI| reflexivity| exact CS| exact RS| exact SSP| exact FRM| left; reflexivity| exact HG| exact TSW| exact ADJ
    | reflexivity| reflexivity| reflexivity| reflexivity| exact K2N|].
  intros p s3 ms3 PO. unfold gentime_adj_post in PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc3 & fc3 & m3 & D & errv3 & junk & -> & FRM3 & FREG3 & MI3 & ST3 & SSP3 & ERR3 & AUX3 & HPB3 & FA3 & SO3 & BRD & HEAP3 & HG3 & HD3 & LJ).
  replace (ret_pc (Z_to_bv 64 1694388)) with (Z_to_bv 64 1694388) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
  pose proof BRD as (D0 & D16 & _ & DC & DI).
  assert (HP3 : rheap_pres (OW ++ LB) (bv_unsigned sp + -96) m2 m3).
  { eapply (rheap_pres_but_other s3 ([(g, G, 24)] ++ OW ++ LB) ((p, D, 20) :: [(g, G, 24)] ++ OW ++ LB) OW LB _ _ m2 m3 g G 24);
      [exact HPB3| reflexivity| exact HEAP3| intros b Hb; right; exact Hb| left; reflexivity| intros b Hb; right; exact Hb| exact NIg| lia]. }
  assert (INV3 : pb_invN s3 m3 [(p, D, 20); (g, G, 24)] errv3 clo nw).
  { eapply (pb_step_nodeN s2 s3 m2 m3 [(g, G, 24)] [(p, D, 20); (g, G, 24)]); [exact INV| exact HP3| cbn [app]; exact HEAP3| exact MI3| exact ST3| exact ERR3| exact AUX3| exact SO3| exact FA3]. }
  assert (HFC3 : sp_F Fc Fc3) by (intros r Hr; rewrite (FREG3 r Hr); reflexivity).
  pose proof (LH_nodup _ _ _ HEAP3) as ND3. cbn [map blk_id fst snd app] in ND3.
  assert (NIp : ~ In p (g :: map blk_id (OW ++ LB))) by (apply NoDup_cons_iff in ND3; exact (proj1 ND3)).
  assert (NEgp : g <> p) by (intros ->; apply NIp; left; reflexivity).
  assert (NEp : p <> pbio) by (intros ->; apply NIp; right; rewrite map_app; apply in_app_iff; left; apply in_map_iff; exists (pbio, out, BIO_SIZE); split; [reflexivity| exact HBIN]).
  pose proof (nb_bio_disjoint _ _ _ p D 20 HEAP3 ltac:(left; reflexivity) (HBL [(p, D, 20); (g, G, 24)]) NEp) as DJD. unfold BIO_SIZE in DJD.
  pose proof (RHEAP_In_ge_4096 _ _ _ p D 20 HEAP3 ltac:(left; reflexivity)) as D4096.
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB INV HPB3 HP3 MI3 ST3 SSP3 ERR3 AUX3 HEAP3 ND2 HG. clear m2.
  pose proof (pb_openN _ _ _ _ _ _ INV3) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  unfold asn1_string_cells, MallocRep.wz in HG3.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m3) as MU. pose proof (wmono_refl ctusegs m3) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply evt_cut.
  { eapply (get0_data_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m3 lo G D [C4 (Z_to_bv 64 15); C4 (Z_to_bv 64 24)] [C8 (Z_to_bv 64 0)]);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact (proj1 HG3)| reflexivity| lia| clear - G16; Z.div_mod_to_equations; lia| lia| lia| reflexivity]. }
  cbv beta. unfold leaf16_post. intros ms' PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & ST4).
  replace (ret_pc (Z_to_bv 64 1694396)) with (Z_to_bv 64 1694396) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (INV4 : pb_invN s3 m4 [(p, D, 20); (g, G, 24)] errv3 clo nw).
  { eapply (pb_step_munchN s3 m3 m4); [exact INV3| exact MU4| exact WM4| | exact MI4| exact ST4| | exact SZ| exact NW|].
    - constructor; [left; cbn; lia| constructor].
    - xport FRL MU4 WM4; [exact FRL| cbn [disjoint_from]; split; [right; lia| exact I]].
    - xport HB MU4 WM4; [exact HB| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL LOB; lia| exact I]]. }
  xport HG3 MU4 WM4; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL LOB; lia| exact I]].
  xport HD3 MU4 WM4; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - DC CEIL LOB; lia| exact I]].
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV3 MU4 WM4 MI4 ST4. clear m3.
  pose proof (pb_openN _ _ _ _ _ _ INV4) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  destruct (magic_lits m4 MI) as [ML1 ML2]. unfold A_MAGIC1, A_MAGIC2 in ML1, ML2.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m4) as MU. pose proof (wmono_refl ctusegs m4) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (ms_reg' ts) by exact TSW.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  destruct (clo_split m4 _ clo FRL SZ) as [FR12 FR20]. replace (bv_unsigned sp + -96 + 12) with (bv_unsigned sp + -84) in FR20 by lia.
  assert (MSR : 0 <= ts_ms ts < 1000) by (pose proof (ts_ms_range ts); lia).
  assert (GB : bytes_at ctusegs m4 D (zb (gen15 t) ++ Z_to_bv 8 0 :: junk)) by (apply (PrnFmt.ro_cells_bytes m4 D 20); exact (proj1 HD3)).
  assert (LJ4 : zlength junk = 4) by (unfold zlength; rewrite LJ; reflexivity).
  zstep. zstep.
  eapply evt_cut.
  { eapply (snprintf_gen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m4 (bv_unsigned sp + -84) 20 A_C18 lo 20%nat _ canary FMT_C18 [PA_s (gen15 t); PA_i (ts_ms ts)] (ct_genstr (gen15 t) (ts_ms ts)));
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold SNPRINTF_STACK, VSN_DEPTH; lia| rewrite ESP; lia| exact SSP| exact FRM3
      | exact FR20| rewrite ESP; lia| unfold GLOBALS_TOP; lia| lia
      | rewrite (zlength_ct_genstr _ _ ltac:(rewrite (zlength_gen15' t) || (unfold zlength; rewrite gen15_length; cbn; lia); lia) MSR); lia| lia
      | rewrite ESP; eapply (sng_C18 m4 lo _ _ _ _ _ _ _ D (gen15 t) (ts_ms ts) junk);
          [exact MI| unfold STATIC_SPLIT; lia| exact GB| exact (gen15_bytes ts t ADJ)| unfold zlength; rewrite gen15_length; reflexivity
          | clear - D16; apply Z.mod_divide; [lia|]; apply Z.mod_divide in D16; [| lia]; destruct D16 as [q Hq]; exists (2 * q); lia
          | exact D4096| lia| lia| lia| exact MSR| reflexivity| rewrite unsigned_lit by lia; apply Z.mod_small; lia]
      | reflexivity| reflexivity| reflexivity]. }
  cbv beta. unfold sng_post. intros ms' PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc5 & fc5 & m5 & -> & MU5 & WM5 & MI5 & FRM5 & FREG5 & ST5 & SSP5 & GEN5).
  replace (ret_pc (Z_to_bv 64 1694456)) with (Z_to_bv 64 1694456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (genstr_some ts t ADJ) in GEN5.
  replace (bv_unsigned sp + -84 + Z.of_nat 20) with (bv_unsigned sp + -64) in MU5 by lia.
  xport FR12 MU5 WM5; [| cbn [disjoint_from cells_size csize Nat.add length]; clear -LOB; lia].
  set (clo5 := [CB 12%nat (firstn 12 (cells_bytes clo))] ++ [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: skipn (S (length (genstr ts))) (skipn 12 (cells_bytes clo)))]).
  assert (INV5 : pb_invN s3 m5 [(p, D, 20); (g, G, 24)] errv3 clo5 nw).
  { eapply (pb_step_munchN s3 m4 m5); [exact INV4| exact MU5| exact WM5| | exact MI5| exact ST5| | reflexivity| exact NW|].
    - constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor].
    - apply rw_cells_app. split; [exact FR12|]. cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -96 + Z.of_nat 12) with (bv_unsigned sp + -84) by lia. exact GEN5.
    - xport HB MU5 WM5; [exact HB| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL; lia| split; [left; clear - OB1 CEIL LOB; lia| exact I]]]. }
  xport HG3 MU5 WM5; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL; lia| split; [left; clear - GC CEIL LOB; lia| exact I]]].
  xport HD3 MU5 WM5; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - DC CEIL; lia| split; [left; clear - DC CEIL LOB; lia| exact I]]].
  assert (HFC5 : sp_F Fc Fc5) by (intros r Hr; rewrite (FREG5 r Hr); apply HFC3; exact Hr).
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV4 MU5 WM5 MI5 ST5 SSP5 FR12 FR20 ML1 ML2 GB. clear m4.
  pose proof (pb_openN _ _ _ _ _ _ INV5) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
    lazymatch EE with (fun pp => ?QQ (fst pp) (snd pp)) => change (implM segs c st0 QQ ms) end end.
  rewrite K2S.
  eapply (T_SETSTR_OK X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m5 s3 ([(p, D, 20); (g, G, 24)] ++ OW ++ LB) lo B errv3 G D (bv_unsigned sp + -84) g p ts _ _ (k3 p) Q);
    [exact HEAP| exact AUX| rewrite ESP; lia| lia| rewrite ESP; exact ST| exact CEIL| unfold GLOBALS_TOP; lia| rewrite ESP; lia
    | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia
    | exact ERR| exact MI| reflexivity| exact CS| exact RS| exact FRM5| right; left; reflexivity| left; reflexivity| exact NEgp
    | exact HG3| exact HD3| exact PRT| exact TSW| exact GEN5| rewrite ESP; lia| lia
    | pose proof SP16 as SP16'; clear - SP16'; apply Z.mod_divide in SP16'; [| lia]; destruct SP16' as [qq Hq]; apply Z.mod_divide; [lia|]; exists (2 * qq - 8); lia
    | reflexivity| reflexivity| exact (K3N p)|].
  intros p' s6 ms6 PO. unfold gentime_setstr_post in PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & errv6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPB6 & FA6 & SO6 & HEAP6 & HG6 & HD6).
  replace (ret_pc (Z_to_bv 64 1694468)) with (Z_to_bv 64 1694468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold LX_ERRNO, RATP in ERR6. change (3355176 - 164) with 3355012 in ERR6.
  cbn [app] in HPB6, HEAP6. rewrite (lb_remove_hd p D 20 ((g, G, 24) :: OW ++ LB) ND3) in HPB6, HEAP6.
  assert (HP6 : rheap_pres (OW ++ LB) (bv_unsigned sp + -96) m5 m6).
  { eapply (rheap_pres_but_other s6 ((g, G, 24) :: OW ++ LB) ((p', D, 19) :: (g, G, 24) :: OW ++ LB) OW LB _ _ m5 m6 g G 24);
      [exact HPB6| reflexivity| exact HEAP6| intros b Hb; right; exact Hb| left; reflexivity| intros b Hb; right; exact Hb| exact NIg| lia]. }
  assert (INV6 : pb_invN s6 m6 [(p', D, 19); (g, G, 24)] errv6 clo5 nw).
  { eapply (pb_step_nodeN s3 s6 m5 m6 [(p, D, 20); (g, G, 24)] [(p', D, 19); (g, G, 24)]); [exact INV5| exact HP6| cbn [app]; exact HEAP6| exact MI6| exact ST6| exact ERR6| exact AUX6| exact SO6| exact FA6]. }
  pose proof (LH_nodup _ _ _ HEAP6) as ND6. cbn [map blk_id fst snd app] in ND6.
  assert (NIp' : ~ In p' (g :: map blk_id (OW ++ LB))) by (apply NoDup_cons_iff in ND6; exact (proj1 ND6)).
  assert (NEgp' : g <> p') by (intros ->; apply NIp'; left; reflexivity).
  assert (NEp' : p' <> pbio) by (intros ->; apply NIp'; right; rewrite map_app; apply in_app_iff; left; apply in_map_iff; exists (pbio, out, BIO_SIZE); split; [reflexivity| exact HBIN]).
  pose proof (nb_bio_disjoint _ _ _ p' D 19 HEAP6 ltac:(left; reflexivity) (HBL [(p', D, 19); (g, G, 24)]) NEp') as DJD'. unfold BIO_SIZE in DJD'.
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB INV5 HPB6 HP6 MI6 ST6 ERR6 AUX6 HEAP6 HG3 HD3 GEN5 ND3 NIp NEp DJD. clear m5.
  pose proof (pb_openN _ _ _ _ _ _ INV6) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & NW6 & HB).
  unfold asn1_string_cells, MallocRep.wz in HG6.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m6) as MU. pose proof (wmono_refl ctusegs m6) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  zstep. if_cases KS1; zify_cond KS1; [exfalso; revert KS1; rewrite ?unsigned_lit by lia; lia|]. clear KS1.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (T_PRINT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m6 lo G D out pv nw ts canary);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia| rewrite ESP; lia| exact SSP| reflexivity| exact FRM5
      | exact HB| unfold obj_range, BIO_SIZE, GLOBALS_TOP; lia| exact NW6| exact NM
      | unfold asn1_string_cells, MallocRep.wz; exact HG6| lia| lia| exact HD6| exact PRT| exact TSW| lia| lia| lia
      | lia| clear - G16; Z.div_mod_to_equations; lia| clear - O16; Z.div_mod_to_equations; lia| reflexivity| reflexivity]. }
  cbv beta. unfold bio_printf_post. intros ms' (r & Hr & PO). rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc7 & fc7 & m7 & -> & MU7 & WM7 & MI7 & FRM7 & FREG7 & ST7 & SSP7 & HB7).
  replace (ret_pc (Z_to_bv 64 1694484)) with (Z_to_bv 64 1694484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite <- bio_null_cells_mod in HB7.
  assert (INV7 : pb_invN s6 m7 [(p', D, 19); (g, G, 24)] errv6 clo5 ((nw + r) mod 2^64)).
  { eapply (pb_step_munchN s6 m6 m7); [exact INV6| exact MU7| exact WM7| | exact MI7| exact ST7| | reflexivity| apply Z.mod_pos_bound; lia| exact HB7].
    - constructor; [left; cbn; lia|]. constructor; [right; cbn; unfold BIO_SIZE; lia| constructor].
    - xport FRL MU7 WM7; [exact FRL| cbn [disjoint_from]; split; [right; lia| split; [right; clear - OB1 CEIL LOB; lia| exact I]]]. }
  xport HG6 MU7 WM7; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL LOB; lia| split; [clear - DJG; lia| exact I]]].
  assert (HFC7 : sp_F Fc Fc7) by (intros rr Hrr; rewrite (FREG7 rr Hrr); apply HFC5; exact Hrr).
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV6 MU7 WM7 MI7 ST7 SSP7 HB7 HD6. clear m6.
  pose proof (pb_openN _ _ _ _ _ _ INV7) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m7) as MU. pose proof (wmono_refl ctusegs m7) as WM.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply (gentime_free_fwd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc7 fc7 m7 lo);
    [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia|].
  intros m8 MU8 WM8 MI8 ST8. rewrite ?ESP in *.
  assert (INV8 : pb_invN s6 m8 [(p', D, 19); (g, G, 24)] errv6 clo5 ((nw + r) mod 2^64)).
  { eapply (pb_step_munchN s6 m7 m8); [exact INV7| exact MU8| exact WM8| | exact MI8| exact ST8| | reflexivity| apply Z.mod_pos_bound; lia|].
    - constructor; [left; cbn; lia| constructor].
    - xport FRL MU8 WM8; [exact FRL| cbn [disjoint_from]; split; [right; lia| exact I]].
    - xport HB MU8 WM8; [exact HB| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; split; [left; clear - OB1 CEIL LOB; lia| exact I]]. }
  xport HG6 MU8 WM8; [| cbn [disjoint_from cells_size csize Nat.add length]; split; [left; clear - GC CEIL LOB; lia| exact I]].
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV7 MU8 WM8 MI8 ST8. clear m7.
  pose proof (pb_openN _ _ _ _ _ _ INV8) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
    lazymatch EE with (fun pp => ?QQ (fst pp) (snd pp)) => change (implM segs c st0 QQ ms) end end.
  rewrite K3S.
  eapply (ASN1_STRING_free_walk HF) with (B := B) (lo := lo) (errv := errv6) (L := [(p', D, 19); (g, G, 24)] ++ OW ++ LB) (pblk := g) (pdata := p') (A := G) (D := D) (alloc := 19) (len := 19) (ty := V_ASN1_GENERALIZEDTIME);
    [exact HEAP| exact AUX| rewrite ESP; lia| rewrite ESP; exact ST| exact CEIL| unfold GLOBALS_TOP; lia
    | rewrite ESP; unfold ASN1_STRING_FREE_STACK, CRYPTO_FREE_STACK, RFREE_STACK; lia
    | exact ERR| exact MI| reflexivity| exact CS| right; left; reflexivity| left; reflexivity| exact NEgp'
    | unfold asn1_string_cells, MallocRep.wz; exact HG6| reflexivity|].
  intros s9 ms9 PO. unfold vfree_post in PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & -> & MI9 & ST9 & ERR9 & AUX9 & HP9 & FA9 & SO9 & HEAP9 & _).
  cbn [app] in HP9, HEAP9. rewrite (lb_remove_hd p' D 19 ((g, G, 24) :: OW ++ LB) ND6) in HP9, HEAP9.
  assert (NDg : List.NoDup (map blk_id ((g, G, 24) :: OW ++ LB))) by (apply NoDup_cons_iff in ND6; exact (proj2 ND6)).
  rewrite (lb_remove_hd g G 24 (OW ++ LB) NDg) in HP9, HEAP9.
  unfold LX_ERRNO, RATP in ERR9. change (3355176 - 164) with 3355012 in ERR9.
  assert (INV9 : pb_invN s9 m9 [] errv6 clo5 ((nw + r) mod 2^64)).
  { eapply (pb_step_nodeN s6 s9 m8 m9 [(p', D, 19); (g, G, 24)] []); [exact INV8| exact HP9| cbn [app]; exact HEAP9| exact MI9| exact ST9| exact ERR9| exact AUX9| exact SO9| exact FA9]. }
  unfold SCT_PRINT_TAIL, MallocRep.wz in KONT.
  replace (ret_pc (Z_to_bv 64 1694492)) with (Z_to_bv 64 1694492) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply KONT; [exact INV9| exact FRM7| exact HFC7].
Qed.

End SPB.
