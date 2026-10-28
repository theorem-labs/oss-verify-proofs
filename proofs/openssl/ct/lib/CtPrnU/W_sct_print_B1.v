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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_prefix_create W_obj_free W_obj_lookup W_asn1_string W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv PrnKit PrnLeaf PrnTimeIface W_sct_print_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition SCT_PRINT_ADJ : Z := 0x19dab0.      (* [comment removed for export] *)
Definition SCT_PRINT_ADJ_RET : Z := 0x19dab4.
Definition A_MAGIC1 : Z := 0x3a788.           (* [comment removed for export] *)
Definition A_MAGIC2 : Z := 0x3a7d0.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCT_PRINT_B_STACK (TSTK : Z) : Z := Z.max 8320 TSTK.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Lemma magic_lits : forall m, mem_inv ctusegs m ->
  ro_cells ctusegs m A_MAGIC1 [C8 (Z_to_bv 64 13992196986280431)] /\ ro_cells ctusegs m A_MAGIC2 [C8 (Z_to_bv 64 2361183241434822607)].
Proof.
  intros m MI. unfold A_MAGIC1, A_MAGIC2. split.
  - eapply W_obj_lookup.ro_cells_recast; [apply (ro_cells_image ctusegs m 239496 ltac:(let bs := eval vm_compute in (match image_bytes ctusegs 239496 8 with Some bs => bs | None => [] end) in exact bs) MI); [vm_compute; reflexivity| lia| cbn; lia]| cbn; tauto| bytes_lit_eq].
  - eapply W_obj_lookup.ro_cells_recast; [apply (ro_cells_image ctusegs m 239568 ltac:(let bs := eval vm_compute in (match image_bytes ctusegs 239568 8 with Some bs => bs | None => [] end) in exact bs) MI); [vm_compute; reflexivity| lia| cbn; lia]| cbn; tauto| bytes_lit_eq].
Qed.

(* [comment removed for export] *)
Lemma swrap32_sint32 : forall x, bv_swrap 32 x = sint32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, sint32. cbn -[Z.modulo Z.add Z.sub Z.ltb Z.pow].
  change (2 ^ Z.of_N 32)%Z with (2^32). change (2 ^ (Z.of_N 32 - 1))%Z with (2^31).
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as B0.
  replace ((x + 2^31) mod 2^32) with ((x mod 2^32 + 2^31) mod 2^32) by (rewrite Z.add_mod_idemp_l by lia; reflexivity).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (x mod 2^32 + 2^31) with ((x mod 2^32 - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma day_reg : forall ts, 0 <= ts < 2^64 ->
  Z.shiftr (Z.land (Z.shiftr (Z.shiftr ts 10 * 13992196986280431) 64) 18446744073709551615) 6 = ts / 86400000.
Proof.
  intros ts Hts. rewrite !Z.shiftr_div_pow2 by lia.
  assert (R1 : 0 <= ts / 2^10 < 2^54) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (R2 : 0 <= ts / 2^10 * 13992196986280431 / 2^64 < 2^64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite land_M64_small by exact R2. rewrite Z.div_div by lia. change (2^64 * 2^6) with (2^70). apply day_magic. exact Hts.
Qed.

Lemma sec_reg : forall ts, 0 <= ts < 2^64 ->
  Z.shiftr (Z.land (Z.land (ts + - Z.land (ts / 86400000 * 86400000) 18446744073709551615) 18446744073709551615 * 274877907) 18446744073709551615) 38 = ts_sec ts.
Proof.
  intros ts Hts. unfold ts_sec, MS_PER_DAY.
  pose proof (Z.div_mod ts 86400000 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound ts 86400000 ltac:(lia)) as MB.
  assert (D0 : 0 <= ts / 86400000) by (apply Z.div_pos; lia).
  rewrite (land_M64_small (ts / 86400000 * 86400000)) by lia.
  replace (ts + - (ts / 86400000 * 86400000)) with (ts mod 86400000) by lia.
  rewrite (land_M64_small (ts mod 86400000)) by lia.
  rewrite land_M64_small by lia. rewrite Z.shiftr_div_pow2 by lia. apply sec_magic. lia.
Qed.

Lemma ms_reg : forall ts, 0 <= ts < 2^64 ->
  Z.land (ts + - Z.land (Z.shiftr (Z.land (Z.shiftr (Z.shiftr ts 3 * 2361183241434822607) 64) 18446744073709551615) 4 * 1000) 18446744073709551615) 18446744073709551615 = ts_ms ts.
Proof.
  intros ts Hts. unfold ts_ms. rewrite !Z.shiftr_div_pow2 by lia.
  assert (R1 : 0 <= ts / 2^3 < 2^61) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (R2 : 0 <= ts / 2^3 * 2361183241434822607 / 2^64 < 2^64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (land_M64_small (ts / 2 ^ 3 * 2361183241434822607 / 2 ^ 64)) by exact R2.
  rewrite Z.div_div by lia. change (2^64 * 2^4) with (2^68). rewrite ms_magic by exact Hts.
  pose proof (Z.div_mod ts 1000 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound ts 1000 ltac:(lia)) as MB.
  assert (D0 : 0 <= ts / 1000) by (apply Z.div_pos; lia).
  rewrite (land_M64_small (ts / 1000 * 1000)) by lia. rewrite land_M64_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma ms_reg' : forall ts, 0 <= ts < 2^64 ->
  ts + - Z.land (Z.shiftr (Z.land (Z.shiftr (Z.shiftr ts 3 * 2361183241434822607) 64) 18446744073709551615) 4 * 1000) 18446744073709551615 = ts_ms ts.
Proof.
  intros ts Hts. unfold ts_ms. rewrite !Z.shiftr_div_pow2 by lia.
  assert (R1 : 0 <= ts / 2^3 < 2^61) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (R2 : 0 <= ts / 2^3 * 2361183241434822607 / 2^64 < 2^64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (land_M64_small (ts / 2 ^ 3 * 2361183241434822607 / 2 ^ 64)) by exact R2.
  rewrite Z.div_div by lia. change (2^64 * 2^4) with (2^68). rewrite ms_magic by exact Hts.
  pose proof (Z.div_mod ts 1000 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound ts 1000 ltac:(lia)) as MB.
  assert (D0 : 0 <= ts / 1000) by (apply Z.div_pos; lia).
  rewrite (land_M64_small (ts / 1000 * 1000)) by lia. lia.
Qed.

Section SPB. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp : word) (m1 : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word).
Variables (K KS : list block) (pbio : bptr) (out pv ts TSTK : Z).

Hypothesis LOB : lo <= bv_unsigned sp - 96 - Z.max 8320 TSTK.    (* [comment removed for export] *)
Hypothesis SPB63 : bv_unsigned sp <= B /\ B < 2^63.
Hypothesis HBIN : In (pbio, out, BIO_SIZE) OW.
Hypothesis NI : ~ In pbio (es_ids st ++ env_ids E).
Hypothesis HK : frozen (forall b, In b K -> In b (OW ++ LB) /\ blk_id b <> pbio).
Hypothesis HKS : frozen (forall b, In b KS -> In b (OW ++ LB) /\ blk_id b <> pbio).
Hypothesis TSW : 0 <= ts < 2^64.
Hypothesis HM : rmalloc_stmt.
Hypothesis HF : rfree_stmt.

(* [comment removed for export] *)
Definition pb_inv (sC : PState) (mC : mem) (NB : list block) (errvC : word) (clo : list cell) (nwC : Z) : Prop :=
  pn_pre sC st mC OW LB E bo NB (bv_unsigned sp + -96) lo B errvC canary
  /\ pn_acc LB (bv_unsigned sp) K s sC m1 mC
  /\ rheap_pres KS (bv_unsigned sp + -64) m1 mC
  /\ rw_cells ctusegs mC (bv_unsigned sp + -96) clo /\ cells_size clo = 32%nat
  /\ 0 <= nwC < 2^64 /\ rw_cells ctusegs mC out (bio_null_cells NULL_METHOD pv nwC).

(* [comment removed for export] *)
Lemma pb_blocks : forall sC mC NB errvC clo nwC, pb_inv sC mC NB errvC clo nwC ->
  0 < out /\ out + 128 <= alloc_ceiling /\ (out + 128 <= 0x10000 \/ 0x355000 <= out)
  /\ (forall b, In b KS -> blk_addr b + blk_size b <= alloc_ceiling /\ (out + 128 <= blk_addr b \/ blk_addr b + blk_size b <= out))
  /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo.
Proof using LOB SPB63 HBIN NI HK HKS TSW.
  intros sC mC NB errvC clo nwC ((HEAP & _ & _ & _ & _ & _ & _ & _ & CEIL & GLO & _) & _).
  assert (HBL : In (pbio, out, BIO_SIZE) (NB ++ OW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; left; exact HBIN).
  pose proof (blk_bounds _ _ _ _ _ _ HEAP HBL) as (B1 & B2 & B3 & B4 & B5). unfold BIO_SIZE in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [| split; [exact CEIL| exact GLO]].
  intros [[p A] n] Hb. pose proof HKS as HKS'. unfold frozen in HKS'. destruct (HKS' _ Hb) as [HbL Hne]. cbn [blk_addr blk_size blk_id fst snd] in *.
  assert (HbL' : In (p, A, n) (NB ++ OW ++ LB)) by (apply in_app_iff; right; exact HbL).
  pose proof (blk_bounds _ _ _ _ _ _ HEAP HbL') as (C1 & C2 & C3 & C4 & C5).
  pose proof (blk_disjoint _ _ _ _ _ _ _ _ _ HEAP HbL' HBL Hne). lia.
Qed.

(* [comment removed for export] *)
Lemma pb_step_munch : forall sC mC mD NB errvC clo clo' nwC nwD W,
  pb_inv sC mC NB errvC clo nwC ->
  munch W mC mD -> wmono ctusegs mC mD ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= bv_unsigned sp + -64) \/ (out <= fst iv /\ snd iv <= out + BIO_SIZE)) W ->
  mem_inv ctusegs mD -> stk ctusegs mD lo (bv_unsigned sp + -96) ->
  rw_cells ctusegs mD (bv_unsigned sp + -96) clo' -> cells_size clo' = 32%nat ->
  0 <= nwD < 2^64 -> rw_cells ctusegs mD out (bio_null_cells NULL_METHOD pv nwD) ->
  pb_inv sC mD NB errvC clo' nwD.
Proof using LOB SPB63 HBIN NI HK HKS TSW.
  intros until W. intros INV MU WM HW MI ST FRL SZ NW HB.
  pose proof (pb_blocks _ _ _ _ _ _ INV) as (OB0 & OB1 & OB2 & KSB & CEIL & GLO). unfold GLOBALS_TOP in GLO.
  destruct INV as (PN & ACC & REL & _ & _ & _ & _).
  pose proof HK as HK'. unfold frozen in HK'.
  destruct (pn_seg_bio sC st mC mD OW LB E bo NB (bv_unsigned sp + -96) (bv_unsigned sp + -96) lo B errvC canary W (bv_unsigned sp) pbio out K
              PN HBIN NI MU WM ltac:(eapply Forall_impl; [| exact HW]; intros iv [[H1 H2]|[H1 H2]]; [left; split; [exact H1| lia]| right; split; assumption])
              ltac:(lia) ltac:(lia) ltac:(lia) MI ST ltac:(intros b Hb; destruct (HK' b Hb) as [H1 H2]; split; [apply in_app_iff; right; exact H1| exact H2]))
    as (PN' & LX & KP).
  split; [exact PN'|]. split.
  { eapply pn_acc_trans; [exact ACC|]. split; [exact LX|]. split; [exact KP|]. split; reflexivity. }
  split.
  { eapply rheap_pres_trans; [exact REL|]. eapply heap_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc. apply seg_outside. eapply Forall_impl; [| exact HW].
    apply rclient_addr_cases in Hc. intros [x y] [[H1 H2]|[H1 H2]]; cbn [fst snd] in *.
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]. pose proof (KSB b Hb). lia.
    - unfold BIO_SIZE in *. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]. pose proof (KSB b Hb). lia. }
  split; [exact FRL|]. split; [exact SZ|]. split; [exact NW| exact HB].
Qed.

(* [comment removed for export] *)
Lemma pb_step_node : forall sC sD mC mD NB NB' (errvC errvD : word) clo nwC,
  pb_inv sC mC NB errvC clo nwC ->
  rheap_pres (OW ++ LB) (bv_unsigned sp + -96) mC mD ->
  RHEAP sD (NB' ++ OW ++ LB) mD -> mem_inv ctusegs mD -> stk ctusegs mD lo (bv_unsigned sp + -96) ->
  rw_cells ctusegs mD 3355012 [C4 errvD] -> rauxv_ok mD B -> ps_so sD = ps_so sC -> ps_fa sD = ps_fa sC ->
  pb_inv sD mD NB' errvD clo nwC.
Proof using LOB SPB63 HBIN NI HK HKS TSW.
  intros until nwC. intros INV HP HEAP' MI' ST' ERR' AUX' SO FA.
  pose proof (pb_blocks _ _ _ _ _ _ INV) as (OB0 & OB1 & OB2 & KSB & CEIL & GLO).
  destruct INV as (PN & ACC & REL & FRL & SZ & NW & HB).
  pose proof HK as HK'. unfold frozen in HK'. pose proof HKS as HKS'. unfold frozen in HKS'.
  destruct (pn_node sC sD st mC mD OW LB E bo NB NB' (bv_unsigned sp + -96) lo B errvC errvD canary (bv_unsigned sp) K
              PN HP HEAP' MI' ST' ERR' AUX' SO FA ltac:(lia) ltac:(intros b Hb; exact (proj1 (HK' b Hb)))) as [PN' ACC'].
  pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
  split; [exact PN'|]. split; [eapply pn_acc_trans; [exact ACC| exact ACC']|].
  split.
  { eapply rheap_pres_trans; [exact REL|]. eapply rheap_pres_weaken; [exact HP| lia| intros b Hb; exact (proj1 (HKS' b Hb))]. }
  split.
  { eapply rw_cells_agree; [exact AG| exact FRL|]. intros a Ha. left. lia. }
  split; [exact SZ|]. split; [exact NW|].
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. right. right. exists (pbio, out, BIO_SIZE).
  split; [apply in_app_iff; left; exact HBIN|]. cbn. rewrite bio_cells_size in Ha. unfold BIO_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma pb_open : forall sC mC NB errvC clo nwC, pb_inv sC mC NB errvC clo nwC ->
  RHEAP sC (NB ++ OW ++ LB) mC /\ ap_state st mC OW E bo /\ rauxv_ok mC B /\ bv_unsigned sp + -96 <= B /\ B < 2^63
  /\ stk ctusegs mC lo (bv_unsigned sp + -96) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
  /\ rw_cells ctusegs mC LX_ERRNO [C4 errvC] /\ ssp_cells mC canary /\ mem_inv ctusegs mC
  /\ crypto_statics mC /\ realloc_statics mC /\ null_meth_cells mC
  /\ rw_cells ctusegs mC (bv_unsigned sp + -96) clo /\ cells_size clo = 32%nat
  /\ 0 <= nwC < 2^64 /\ rw_cells ctusegs mC out (bio_null_cells NULL_METHOD pv nwC).
Proof using LOB SPB63 HBIN NI HK HKS TSW.
  intros sC mC NB errvC clo nwC ((HEAP & AS & IDS & DC & AUX & QB & B63 & ST & CEIL & GLO & LOQ & ERR & SSP & MI) & _ & _ & FRL & SZ & NW & HB).
  pose proof AS as (_ & IMG & (CS & RS & _) & _).
  unfold LX_ERRNO, RATP. change (3355176 - 164) with 3355012.
  repeat (split; [assumption|]). split; [apply null_meth_of_img; [exact MI| exact IMG]|]. repeat (split; [assumption|]). exact HB.
Qed.

(* [comment removed for export] *)
Lemma seg_B1 : forall {X : Type} (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (errv1 : word) (clo : list cell) (nw1 : Z)
    (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
  pb_inv s m1 [] errv1 clo nw1 -> frm0 fc -> k None = LUnr ->
  (forall (g : bptr) (G : Z) (s2 : PState) (m2 : mem) (errv2 x1' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     pb_inv s2 m2 [(g, G, 24)] errv2 clo nw1 -> rblock_range G 24 ->
     rw_cells ctusegs m2 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
     implM ctusegs (interp (k (Some g))) s2 Q
       (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0' t1' t2' sp (Z_to_bv 64 out)
                (Z_to_bv 64 G) (Z_to_bv 64 0) (Z_to_bv 64 (ts_day ts)) (Z_to_bv 64 (ts_sec ts)) a4' a5' a6' a7'
                x18 x19 x20 (Z_to_bv 64 G) (Z_to_bv 64 ts) x23 x24 x25 x26 x27 t3' t4' t5' t6')
           Fc (Z_to_bv 64 SCT_PRINT_ADJ) fc None m2 (seg_rom ctusegs))) ->
  implM ctusegs (interp (LMalloc 24 k)) s Q
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 (Z_to_bv 64 ts) x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_PRINT_TS) fc None m1 (seg_rom ctusegs)).
Proof using LOB SPB63 HBIN NI HK HKS TSW HM.
  intros until Q. intros INV FRM KN KONT.
  pose proof (pb_blocks _ _ _ _ _ _ INV) as (OB0 & OB1 & OB2 & KSB & CEIL & GLO). unfold GLOBALS_TOP in GLO.
  pose proof (pb_open _ _ _ _ _ _ INV) as (HEAP & AS & AUX & QB & B63 & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & SZ & NW & HB). cbn [app] in HEAP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  unfold SCT_PRINT_TS, MallocRep.wz.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  zstep.
  eapply (gentime_new_fwd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m1 lo);
    [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia|].
  intros m1' MU1 WM1 MI1 ST1. rewrite ?ESP in *.
  (* [comment removed for export] *)
  assert (INV1 : pb_inv s m1' [] errv1 clo nw1).
  { eapply (pb_step_munch s m1 m1' [] errv1 clo clo nw1 nw1); [exact INV| exact MU1| exact WM1| | exact MI1| exact ST1| | exact SZ| exact NW|].
    - constructor; [| constructor]. left. cbn. lia.
    - eapply rw_cells_transport; [exact FRL| exact MU1| exact WM1| cbn [disjoint_from]; lia].
    - eapply rw_cells_transport; [exact HB| exact MU1| exact WM1| cbn [disjoint_from]; rewrite bio_cells_size; unfold BIO_SIZE; lia]. }
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB MU WM INV.
  pose proof (pb_open _ _ _ _ _ _ INV1) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB). cbn [app] in HEAP.
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
  eapply (ASN1_STRING_type_new_walk HM) with (B := B) (lo := lo) (errv := errv1) (L := OW ++ LB);
    [exact HEAP| exact AUX| rewrite ESP; lia| rewrite ESP; exact ST| exact CEIL| unfold GLOBALS_TOP; lia
    | rewrite ESP; unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
    | exact ERR| exact MI| reflexivity| exact CS| reflexivity| unfold V_ASN1_GENERALIZEDTIME; lia| exact KN|].
  intros g s2 ms2 PO. unfold calloc_post in PO. rewrite ?ESP in PO.
  destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & G & errv2
                  & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & FA2 & SO2 & BR2 & HEAP2 & BLK2).
  replace (ret_pc (Z_to_bv 64 1694312)) with (Z_to_bv 64 1694312) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
  assert (INV2 : pb_inv s2 m2 [(g, G, 24)] errv2 clo nw1).
  { eapply (pb_step_node s s2 m1' m2 [] [(g, G, 24)]); [exact INV1| exact HP2| cbn [app]; exact HEAP2| exact MI2| exact ST2| exact ERR2| exact AUX2| exact SO2| exact FA2]. }
  pose proof BR2 as (G0 & G16 & _ & GC & GI).
  clear HEAP AS AUX ST ERR SSP MI CS RS NM FRL HB INV1 HP2 MU1 WM1 MI1 ST1. clear m1'.
  pose proof (pb_open _ _ _ _ _ _ INV2) as (HEAP & AS & AUX & _ & _ & ST & _ & _ & ERR & SSP & MI & CS & RS & NM & FRL & _ & _ & HB).
  destruct (magic_lits m2 MI) as [ML1 ML2]. unfold A_MAGIC1, A_MAGIC2 in ML1, ML2.
  pose proof (munch_refl [(lo, bv_unsigned sp + -96)] m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]. clear K0.
  (* [comment removed for export] *)
  zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (day_reg ts), (sec_reg ts) by exact TSW.
  zstep. rewrite Z.add_0_r, swrap32_sint32. change (sint32 (ts / 86400000)) with (ts_day ts).
  zstep. zstep.
  apply evt_done. unfold SCT_PRINT_ADJ, MallocRep.wz in KONT.
  eapply (KONT g G s2 m2 errv2); [exact INV2| exact BR2| exact BLK2].
Qed.

End SPB.
