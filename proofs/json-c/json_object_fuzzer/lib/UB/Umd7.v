(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qazd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULLZ UAIk.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Lh2 Require Lh2InsStmt Lh2InsTail.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_insert_entry : Z := 0x285a8.
Definition lh_resize_entry : Z := 0x2840c.

Definition strip (e : lent) : Z * Z * list byte * Z := (le_k e, le_kn e, le_ks e, le_v e).

#[using="Type"] Lemma fsaved_caller_saved3 : forall F a b c,
QCcH.fsaved F (bvmap_set 13 a (bvmap_set 14 b (bvmap_set 15 c F))).
Proof.
intros F a b c j Hj. cbn in Hj.
assert (Hj' : j <> 13 /\ j <> 14 /\ j <> 15) by lia.
rewrite !QEpW.reg_get_set_other; [reflexivity | | |];
intros E; apply (f_equal bv_unsigned) in E; revert E;
repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] | H : False |- _ => destruct H end; vm_compute; lia.
Qed.

#[using="Type"] Lemma fsaved_set_other : forall F G (j : bv 5) x,
forallb (fun i => negb (bv_unsigned j =? i)) QCcH.FSAVED = true -> QCcH.fsaved F G -> QCcH.fsaved F (bvmap_set j x G).
Proof.
intros F G j x Hj FS i Hi. rewrite QEpW.reg_get_set_other; [exact (FS i Hi)|].
intros E. subst j. rewrite forallb_forall in Hj. specialize (Hj i Hi). cbn in Hi.
repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] | H : False |- _ => destruct H end; vm_compute in Hj; discriminate.
Qed.

Local Ltac ins_fsaved := repeat (apply fsaved_set_other; [vm_compute; reflexivity|]); apply QCcH.fsaved_refl.
Local Ltac ins_br := first [if_true | if_false | if_truex | if_falsex].

Section LhInsert2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).
Hypothesis LF : lf_test_spec.

Variable MREL : Model -> Model -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only a b -> MREL a b.

Definition lh_resize_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo t tbl size ns : Z) (es : list lent) (svs : list slotv)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\ lh_glob4 m' /\
( (r = 2^64 - 1 /\ lh_open rsegs S4F m' t tbl size es svs /\ HEAPx A' (lh_blocks t tbl size es ++ LB) m' md')
\/ (r = 0 /\ exists tbl' es' svs', map strip es' = map strip es /\
lh_open rsegs S4F m' t tbl' ns es' svs' /\ HEAPx A' (lh_blocks t tbl' ns es' ++ LB) m' md') ).

Definition lh_resize_stmt (RD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size ns : Z) (es : list lent) (svs : list slotv),
HEAPx A (lh_blocks t tbl size es ++ LB) m md ->
lh_open rsegs S4F m t tbl size es svs -> lh_glob4 m ->
In ns lf_sizes -> lf_thr size + 1 <= lf_thr ns ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 ns ->
(forall ms' md', lh_resize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size ns es svs ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_resize_entry) fc None m (seg_rom rsegs)) md) T.

Definition lh_insert_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\ lh_glob4 m' /\
( (r = 2^64 - 1 /\ lh_open rsegs S4F m' t tbl size es svs /\ cstr rsegs m' k kn ks /\
HEAPx A' (lh_blocks t tbl size es ++ (k, kn) :: LB) m' md')
\/ (r = 0 /\ exists tbl' size' es' svs' (g : nat), map strip es' = map strip es /\
lh_open rsegs S4F m' t tbl' size' (es' ++ [LE g k kn ks v]) svs' /\
HEAPx A' (lh_blocks t tbl' size' (es' ++ [LE g k kn ks v]) ++ LB) m' md') ).

Definition lh_insert_fix_post (ffn : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (errv' : word) svs' (g : nat),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
MREL md md' /\ stk rsegs m' lo (bv_unsigned sp) /\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\ lh_glob4 m' /\
lh_openf rsegs S4F ffn m' t tbl size (es ++ [LE g k kn ks v]) svs' /\
HEAPx A' (lh_blocks t tbl size (es ++ [LE g k kn ks v]) ++ LB) m' md'.

#[using="Type"] Lemma lf_size_cases : forall S, In S lf_sizes -> S <= 2^29 \/ S = 1073741824 \/ S = 2147483647.
Proof.
intros S H.
assert (C : forallb (fun S => (S <=? 2^29) || (S =? 1073741824) || (S =? 2147483647)) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply orb_prop in C as [C|C]; [apply orb_prop in C as [C|C]|];
[left; apply Z.leb_le; exact C | right; left; apply Z.eqb_eq; exact C | right; right; apply Z.eqb_eq; exact C].
Qed.

Section Finish.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t : Z).
Variables (k kn : Z) (ks : list byte) (v : Z) (T : TSet) (ffn : Z).
Hypothesis Hffn : 0 <= ffn < 2^64.
Hypothesis Hkn : kn <= 2^31.

#[using="Hffn Hkn"] Lemma lh_insert_finish :
  forall (tbl size : Z) (es : list lent) (svs : list slotv) (h : Z)
    (x1 x5 x6 x7 x8 x9 x15 x17 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word),
  HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
  lh_openf rsegs S4F ffn m t tbl size es svs ->
  Z.of_nat (length es) + 1 <= lf_thr size ->
  cstr rsegs m k kn ks -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
  lh_glob4 m ->
  stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
  bv_unsigned ra mod 2 = 0 ->
  QCcH.fsaved F F1 -> (QCcH.frm0 fc -> QCcH.frm0 fc1) ->
  MREL md0 md -> heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 m ->
  (forall ms' md', lh_insert_fix_post ffn ra sp gp (Z_to_bv 64 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es k kn ks v ms' md' ->
     realizes rsegs (mkCfg ms' md') T) ->
  realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0x77c00) x5 x6 x7 x8 x9
        (Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) x15 (Z_to_bv 64 size) x17
        x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F1 (Z_to_bv 64 0x28660) fc1 None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP OPEN ROOM CS Hv Hh G ST LO LOS FR ERR RA FS FRM VM0 HPR K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.

assert (HinK : In (k, kn) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ k kn HP HinK) as (Hkn0 & Hkal & Hklo & Hkhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ k kn HP HinK) as Hkimg. cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
pose proof CS as (CSL & CSNZ & junkk & CSB).
apply rz_evt; [exact MOK|].
eapply evt_cut.
{ eapply (Lh2InsTail.u_lh_insert_tail_img sp gp (Z_to_bv 64 490496) s5 s6 s7 s8 s9 s10 s11 F1 fc1 t tbl size k v 0 es svs ffn ra s0 s1 s2 s3 s4
    (Lh2InsTail.lh_store_block_img sp gp (Z_to_bv 64 490496) s5 s6 s7 s8 s9 s10 s11 F1 fc1 t tbl size k v 0 svs ffn ra s0 s1 s2 s3 s4)
    h (Z.of_nat (length es)) lo);
  first [exact Hsz | exact Hlen | exact LINK | exact KEYS | exact MI | exact SL | exact FR | exact ST | exact SEP | exact Hffn
        | exact Htal | exact Hbal | reflexivity | lia | idtac].
  unfold Lh2InsStmt.hdr_cells. unfold lh_hdrf in HDR. exact HDR. }
cbv beta. intros ms' (g & sg & ixl & sl & x5' & x6' & x7' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m'
  & Hg & Esg & FREE & NIN & LAST & -> & MU & WM & MI' & HDR' & SL' & ST').
destruct (lh_newkey_facts S4L HIx _ _ _ _ _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DKt & DKb & NK).

assert (ERR' : rw_cells rsegs m' (490496 - 164) [C4 errv]).
{ eapply (rw_cells_transport rsegs _ m m'); [exact ERR | exact MU | exact WM |]. cbn. lia. }
assert (G' : lh_glob4 m').
{ eapply (lh_glob_frame rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4 m m'); [exact G | exact MU | exact WM |]. unfold GHASH4, GGOT4, GVDSO4.
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
assert (KEYS' : lh_keys rsegs m' es).
{ eapply (lh_keys_frame rsegs m m'); [exact KEYS | exact MU | exact WM |]. intros e He. destruct (KF e He) as (? & ? & ? & ? & ? & ?).
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
assert (CS' : cstr rsegs m' k kn ks).
{ split; [exact CSL|]. split; [exact CSNZ|]. exists junkk. eapply (rw_cells_transport rsegs _ m m'); [exact CSB | exact MU | exact WM |].
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf). cbn. lia. }
apply evt_RZ_done. apply K. unfold lh_insert_fix_post.
exists m', A, errv, (ULLZ.ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl), g.
split; [| split; [exact VM0 | split; [exact ST' | split; [| split; [exact ERR' | split; [exact G' | split]]]]]].
- unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS | exact FRM].
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch S4L s4_volatile LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; right; exact Hb | clia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; right; left.
+ exists t, 56. split; [left; reflexivity|]. split; [| lia].
intros IN. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) LB t 56 56); [rewrite <- app_assoc; exact ND | apply in_or_app; left; left; reflexivity | exact IN].
+ exists tbl, (40 * size). split; [right; left; reflexivity|]. split; [| lia].
intros IN. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) LB tbl (40 * size) (40 * size)); [rewrite <- app_assoc; exact ND | apply in_or_app; left; right; left; reflexivity | exact IN].
- eapply UAIk.lh_open_snoc; try eassumption; try lia.
split; [lia|]. split; [unfold LH_FREEDv; lia | exact Hkn].
- eapply heap_perm.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; right; left;
[exists t, 56; split; [left; reflexivity | lia] | exists tbl, (40 * size); split; [right; left; reflexivity | lia]].
+ unfold lh_blocks. rewrite map_app. cbn [map app le_k le_kn].
apply perm_skip. apply perm_skip.
change (map (fun e : lent => (le_k e, le_kn e)) es ++ (k, kn) :: LB) with (map (fun e : lent => (le_k e, le_kn e)) es ++ [(k, kn)] ++ LB).
rewrite app_assoc. apply Permutation_refl.
Qed.
End Finish.

#[using="LF"] Lemma lh_insert_prologue :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t tbl size : Z) (es : list lent) (svs : list slotv) (lo ffn : Z),
mem_inv rsegs m -> frm0 fc ->
lh_openf rsegs S4F ffn m t tbl size es svs -> lh_below lo t tbl size es -> 0 < t -> t mod 16 = 0 ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 ->
evt rsegs (fun ms' => exists F' fc' m' a7',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4
(bword (lf_thr size <=? Z.of_nat (length es))) (Z_to_bv 64 size) a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x285f0) fc' None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ QCcH.fsaved F F' /\ frm0 fc'
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ lh_openf rsegs S4F ffn m' t tbl size es svs)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_entry) fc None m (seg_rom rsegs)).
Proof.
intros until ffn. intros MI FRM OPEN BELOW Htpos Htal ST LOS.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdrf in HDR. pose proof BELOW as (Ht0 & Ht & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof (rw_cells_bound rsegs m t _ HDR) as TB. cbn [cells_size csize Nat.add] in TB.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold lh_insert_entry.
carve_frame 48%nat ST.
do 7 step.
step. if_falsex.
step. step. ubsan_align Htal.
step. norm_sx32. step. norm_sx32.
do 6 step.
change (fle_d _ _) with (lf_test RNE size (Z.of_nat (length es))). rewrite (LF size (Z.of_nat (length es)) Hsz ltac:(lia)).
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [ins_fsaved|]. split; [assumption|]. split; [eassumption|]. split; [exact ST|].
lazymatch goal with |- lh_openf _ _ _ ?mx _ _ _ _ _ => eapply (lh_open_frame rsegs S4F ffn m mx) end;
[exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
Qed.

#[using="LF MREL_refl"] Lemma lh_insert_cps : forall (RD : Z), lh_resize_stmt RD -> 0 <= RD ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h : Z),
HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
lh_open rsegs S4F m t tbl size es svs -> lh_glob4 m -> cstr rsegs m k kn ks -> kn <= 2^31 ->
0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
(forall ms' md', lh_insert_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size es svs k kn ks v ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros RD RESIZE HRD. intros until h. intros HP OPEN G CS Hkn Hv Hh ST LO LOS SPA HT ERR TP RA FRM A0 A1 A2 A3 A4 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
destruct (lh_newkey_facts S4L HIx _ _ _ _ _ _ _ _ _ _ HP) as (Hkn0 & Hklo & Hkhi & Hkimg & DKt & DKb & NK).
cbn [hl_img_lo hl_img_hi S4L] in Hkimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). (clear - LO H0; lia). }
destruct G as ([seed G1] & G2 & (vf & G3 & VF)). unfold GHASH4 in G1. unfold GGOT4 in G2. unfold GVDSO4 in G3.
pose proof CS as (CSL & CSNZ & junkk & CSB).
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf).
pose proof (heap_presx_refl S4L s4_volatile LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst a0 a1 a2 a3 a4 tp.
call lh_insert_prologue; [exact MI | exact FRM | exact OPEN | exact BELOW | lia | exact Htal | exact ST | lia |].
match goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM1 end.
match goal with H : QCcH.fsaved F ?f |- evt _ _ (MS _ ?f _ _ _ _ _) => rename H into FS1 end.
match goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -48) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FR1 end.
match goal with H : stk rsegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
match goal with H : lh_openf rsegs S4F _ ?mx _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono rsegs m m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m1 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU1). solve_frameW_with HP. }
assert (HPR1 : heap_presx S4L s4_volatile LB (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch S4L s4_volatile LB (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP. }
assert (G1' : lh_glob4 m1) by (split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]]).
assert (CS1 : cstr rsegs m1 k kn ks) by (split; [exact CSL|]; split; [exact CSNZ|]; exists junkk; exact CSB).
step.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))) as [GE | LT].
-
cbn [bword]. if_false.
assert (EQC : Z.of_nat (length es) = lf_thr size) by lia.
destruct (Z.eq_dec size 2147483647) as [EMAX | NMAX].
{
step. step. step. ins_br.
step. step. step. ins_br.
step. step. step.
step. do 7 step.
release_frame FR1 ST1 (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold lh_insert_post.
exists m1, A, (2^64 - 1), errv.
split; [| split; [apply MREL_refl | split; [exact ST1 | split; [exact HPR1 | split; [| split; [exact G1' | left]]]]]].
* unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [exact FS1 | intros H0; exact FRM1].
* exact ERR.
* split; [reflexivity|]. split; [exact OPEN1|]. split; [exact CS1 | exact HP1]. }
lazymatch goal with |- evt _ _ (MS ?R ?FR _ ?fcx ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms' => exists ns, In ns lf_sizes /\ lf_thr size + 1 <= lf_thr ns /\
ms' = MS (bvmap_set 15 (Z_to_bv 64 ns) R) FR (Z_to_bv 64 0x28620) fcx rv mm ro) end.
{ destruct (lf_size_cases size Hsz) as [S29 | [S30 | SMAX]]; [| | exfalso; exact (NMAX SMAX)].
- destruct (lf_thr_step size Hsz S29) as [Hsz2 Hthr2].
step. step. step. ins_br.
step. step. step. if_falsex.
step. rewrite ?(unsigned_lit size) by lia. rewrite ?(Z.shiftl_mul_pow2 size 1) by lia. try change (2 ^ 1) with 2. rewrite ?swrap32_id by lia.
apply evt_done. exists (2 * size). split; [exact Hsz2|]. split; [exact Hthr2|]. replace (size * 2) with (2 * size) by lia. reflexivity.
- step. step. step. ins_br. step. step. step. ins_br.
apply evt_done. exists 2147483647. split; [unfold lf_sizes; cbn [In]; do 27 right; left; reflexivity|].
split; [rewrite S30; apply lf_thr_top | reflexivity]. }
cbv beta. intros ms' (ns & HszN & HthrN & ->).
pose proof (lf_size_range ns HszN) as HSRN.
do 6 step. step.

apply evt_RZ_done. eapply (RESIZE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md T A ((k, kn) :: LB) lo _ t tbl size ns es svs);
try alloc_side; first [exact HP1 | exact OPEN1 | exact G1' | exact HszN | exact HthrN | lia | exact FRM1 | apply bv_eq; rewrite !unsigned_lit by lia; lia | idtac].
intros ms2 md2 (m2 & A2 & r & errv2 & RS & VM2 & ST2 & HPR2 & ERR2 & GL2 & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2). cbn [hl_segs S4L] in *.
rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, HPR2 by lia.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
assert (HPR' : heap_presx S4L s4_volatile LB (bv_unsigned sp) m m2).
{ eapply heap_presx_trans; [exact HPR1|]. eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; right; exact Hb | intros a' Ha'; exact Ha']. }

assert (CS2 : cstr rsegs m2 k kn ks).
{ split; [exact CSL|]. split; [exact CSNZ|]. exists junkk. eapply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2); [exact CSB |].
eapply client_rangex_block; [left; reflexivity | lia | cbn; lia]. }
destruct OUT as [(-> & OPEN2 & HP2) | (-> & tbl' & es' & svs' & STRIP & OPEN2 & HP2)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl rsegs m2) as WM2.
reenter MOK2.
replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 18446744073709551615) by reflexivity.
step. ins_br. step. step.
step. do 7 step.
release_frame FR1 ST2 (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold lh_insert_post.
exists m2, A2, (2^64 - 1), errv2.
split; [| split; [exact VM2 | split; [exact ST2 | split; [exact HPR' | split; [exact ERR2 | split; [exact GL2 | left]]]]]].
* unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [| intros H0; apply FRM2; exact FRM1].
eapply QCcH.fsaved_trans; [exact FS1 | exact FS2].
* split; [reflexivity|]. split; [exact OPEN2|]. split; [exact CS2 | exact HP2].
+
pose proof OPEN2 as (HDR2 & _ & _ & _ & Hsz2' & Hcnt2 & Hlen2). unfold lh_hdr, lh_hdrf in HDR2.
pose proof (lf_size_range ns HszN) as HSR2.
assert (LEN2 : length es' = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl rsegs m2) as WM2.
reenter MOK2.
step. ins_br.
step. step. norm_sx32. step. step. step. step.
apply evt_RZ_done.
eapply (lh_insert_finish ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t k kn ks v T (fn_lh_entry_free S4F) ltac:(cbn; (clear; lia)) Hkn tbl' ns es' svs' h);
first [exact HP2 | exact OPEN2 | exact CS2 | exact GL2 | exact ST2 | exact ERR2 | exact RA | exact VM2 | exact HPR' | exact FR1 | (clear - EQC HthrN LEN2 Hv Hh LO HRD LOS; lia) | idtac].

all: try clia.
all: try (eapply QCcH.fsaved_trans; [exact FS1 | exact FS2]).
all: try (intros H0; apply FRM2; exact FRM1).
intros ms' md' (m' & A' & errv' & svs'' & g & RS' & MR & ST' & HPR'' & ERR' & G' & OPEN' & HP'). apply K. unfold lh_insert_post.
exists m', A', 0, errv'. repeat (split; [assumption|]). right. split; [reflexivity|]. exists tbl', ns, es', svs'', g. split; [exact STRIP|]. split; assumption.
-
cbn [bword]. if_true.
apply evt_RZ_done.
eapply (lh_insert_finish ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t k kn ks v T (fn_lh_entry_free S4F) ltac:(cbn; lia) Hkn tbl size es svs h);
first [exact HP1 | exact OPEN1 | exact CS1 | exact G1' | exact ST1 | exact FR1 | exact RA | exact FS1
| apply MREL_refl | exact HPR1 | lia | idtac].
all: try eassumption. all: try (intros _; assumption). all: try clia.

intros ms' md' (m' & A' & errv' & svs' & g & RS & MR & ST' & HPR' & ERR' & G' & OPEN' & HP'). apply K. unfold lh_insert_post.
exists m', A', 0, errv'. repeat (split; [assumption|]). right. split; [reflexivity|]. exists tbl, size, es, svs', g. split; [reflexivity|]. split; assumption.
Qed.

#[using="LF MREL_refl"] Lemma lh_insert_small_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h ffn : Z),
HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
lh_openf rsegs S4F ffn m t tbl size es svs -> lh_glob4 m -> cstr rsegs m k kn ks -> kn <= 2^31 -> 0 <= ffn < 2^64 ->
Z.of_nat (length es) + 1 <= lf_thr size -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
(forall ms' md', lh_insert_fix_post ffn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size es k kn ks v ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until ffn. intros HP OPEN G CS Hkn Hffn HcntS Hv Hh ST LO LOS SPA HT ERR TP RA FRM A0 A1 A2 A3 A4 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
destruct (lh_newkey_facts S4L HIx _ _ _ _ _ _ _ _ _ _ HP) as (Hkn0 & Hklo & Hkhi & Hkimg & DKt & DKb & NK).
cbn [hl_img_lo hl_img_hi S4L] in Hkimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). (clear - LO H0; lia). }
destruct G as ([seed G1] & G2 & (vf & G3 & VF)). unfold GHASH4 in G1. unfold GGOT4 in G2. unfold GVDSO4 in G3.
pose proof CS as (CSL & CSNZ & junkk & CSB).
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf).
pose proof (heap_presx_refl S4L s4_volatile LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst a0 a1 a2 a3 a4 tp.
call lh_insert_prologue; [exact MI | exact FRM | exact OPEN | exact BELOW | lia | exact Htal | exact ST | lia |].
match goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM1 end.
match goal with H : QCcH.fsaved F ?f |- evt _ _ (MS _ ?f _ _ _ _ _) => rename H into FS1 end.
match goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -48) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FR1 end.
match goal with H : stk rsegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
match goal with H : lh_openf rsegs S4F _ ?mx _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono rsegs m m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m1 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU1). solve_frameW_with HP. }
assert (HPR1 : heap_presx S4L s4_volatile LB (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch S4L s4_volatile LB (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP. }
assert (G1' : lh_glob4 m1) by (split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]]).
assert (CS1 : cstr rsegs m1 k kn ks) by (split; [exact CSL|]; split; [exact CSNZ|]; exists junkk; exact CSB).
step.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))) as [GE | LT].
-  exfalso. lia.
-
cbn [bword]. if_true.
apply evt_RZ_done.
eapply (lh_insert_finish ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t k kn ks v T ffn Hffn Hkn tbl size es svs h);
first [exact HP1 | exact OPEN1 | exact CS1 | exact G1' | exact ST1 | exact FR1 | exact RA | exact FS1
| apply MREL_refl | exact HPR1 | exact K | lia | idtac].
all: try eassumption. all: try (intros _; assumption). all: try clia.
Qed.

End LhInsert2.

End RC__1.
