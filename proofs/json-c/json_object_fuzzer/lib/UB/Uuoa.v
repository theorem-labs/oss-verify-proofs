(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup UEQM Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH UC8c Qsw7 QJjn UBpZ UT7i Uv6q UD4E UzWc Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q UD4E.
Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SER_BOOL : Z := 0x24984.
Definition SER_DBL : Z := 0x24a40.
Definition SER_DBLF : Z := 0x25d60.
Definition SER_INT : Z := 0x24a4c.
Definition SER_STR : Z := 0x252c4.
Definition SER_OBJ : Z := 0x24ac0.
Definition SER_ARR : Z := 0x24ed4.
Definition SER_UD : Z := 0x26150.
Definition SER_EXT : Z := 0x253bc.
Definition GET_STRING : Z := 0x265bc.
Definition MEMAPPEND : Z := 0x241a4.
Definition PBMEMSET : Z := 0x243b8.
Definition PBNEW : Z := 0x24134.
Definition PBRESET : Z := 0x245cc.
Definition ESCAPE : Z := 0x26fb4.
Definition STRLEN : Z := 0x5fc5c.
Definition SNPRINTF : Z := 0x5514c.
Definition ERRNO : Z := 490332.
Definition TP : Z := 0x77c00.

Definition fn_of (s : jshape) : Z :=
match s with
| Sbool => SER_BOOL | Sdouble false => SER_DBL | Sdouble true => SER_UD | Sint => SER_INT
| Sstr _ => SER_STR | Sobj _ => SER_OBJ | Sarr _ => SER_ARR
end.

Definition fn_ofF (fn : fnaddrs) (s : jshape) : Z :=
match s with
| Sbool => fn_bool_to_json_string fn | Sdouble false => fn_dbl_to_json_string fn
| Sdouble true => fn_ud_to_json_string fn | Sint => fn_int_to_json_string fn
| Sstr _ => fn_str_to_json_string fn | Sobj _ => fn_obj_to_json_string fn | Sarr _ => fn_arr_to_json_string fn
end.
#[using="Type"] Lemma fn_of_S4F : forall s, fn_ofF S4F s = fn_of s.
Proof. destruct s as [|[|]| |h|k|k]; reflexivity. Qed.
#[using="Type"] Lemma fn_of_even : forall s, fn_of s mod 2 = 0.
Proof. destruct s as [|[|]| |h|k|k]; reflexivity. Qed.
#[using="Type"] Lemma fn_of_range : forall s, 0 <= fn_of s < 2^20.
Proof. destruct s as [|[|]| |h|k|k]; cbn -[Z.pow Z.le Z.lt]; unfold SER_BOOL, SER_DBL, SER_UD, SER_INT, SER_STR, SER_OBJ, SER_ARR; lia. Qed.

Definition flags_ok (fl : Z) : Prop := 0 <= fl < 2^31 /\ Z.land fl 56 = 0.

Definition lb_small (LB : list blk) : Prop := True.

Definition ser_budget (s : jshape) : Z := 208 * sdepth s + 8560.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation rw_cells := (rw_cells segs).
Notation jvalx := (jval segs fn).

Definition kids_okv (m : word -> option byte) :=
fix kids_ok (ks : list (option jshape)) (vs : list (Z * Z)) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', (_, v) :: vs', bs :: bss' =>
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end /\ kids_ok ks' vs' bss'
| _, _, _ => False
end.
Definition kids_okp (m : word -> option byte) :=
fix kids_ok (ks : list (option jshape)) (vs : list Z) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', v :: vs', bs :: bss' =>
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end /\ kids_ok ks' vs' bss'
| _, _, _ => False
end.

#[using="Type"] Lemma kids_okv_cons : forall m k ks kk v vs bs bss,
kids_okv m (k :: ks) ((kk, v) :: vs) (bs :: bss) =
(match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end /\ kids_okv m ks vs bss).
Proof. reflexivity. Qed.

#[using="Type"] Lemma kids_okp_cons : forall m k ks v vs bs bss,
kids_okp m (k :: ks) (v :: vs) (bs :: bss) =
(match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end /\ kids_okp m ks vs bss).
Proof. reflexivity. Qed.

Definition jnode (s : jshape) (m : word -> option byte) (REST : list blk) (p rc pb0 : Z) : Prop :=
match s with
| Sbool =>
exists (b : Z) junk, REST = [(p, 48)] /\
rw_cells m p (jhdr_cells JT_BOOLEAN rc (fn_bool_to_json_string fn) pb0 0 0 ++ [C4 (wz b); CB 4 junk])
| Sdouble false =>
exists (bits : word), REST = [(p, 48)] /\ dbl_special bits /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string fn) pb0 0 0 ++ [C8 bits])
| Sdouble true =>
exists (bits : word) (ud udn : Z) (uds : list byte), REST = [(p, 48); (ud, udn)] /\ udn <= 2^31 /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_ud_to_json_string fn) pb0 (fn_free_userdata fn) ud ++ [C8 bits]) /\
cstr segs m ud udn uds
| Sint =>
exists (cty : Z) (v : word) junk, REST = [(p, 56)] /\ (cty = 0 \/ cty = 1) /\
rw_cells m p (jhdr_cells JT_INT rc (fn_int_to_json_string fn) pb0 0 0 ++ [C4 (wz cty); CB 4 junk; C8 v])
| Sstr false =>
exists (len : Z) (str : list byte) junk, REST = [(p, str_objsize len)] /\ 0 <= len < 2^31 /\ Z.of_nat (length str) = len /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb0 0 0 ++
[C8 (wz len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)])
| Sstr true =>
exists (len : Z) (pd pdn : Z) (str : list byte) junk2, REST = [(p, 56); (pd, pdn)] /\
- 2^31 < len < 0 /\ Z.of_nat (length str) = - len /\ - len + 1 <= pdn /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb0 0 0 ++ [C8 (wz len); C8 (wz pd)]) /\
rw_cells m pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]
| Sobj kids =>
exists (t : Z) (TBS : list blk) (kvs : list (Z * Z)) (KBS : list (list blk)),
REST = (p, 48) :: TBS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb0 0 0 ++ [C8 (wz t)]) /\
lhtab2 segs fn m TBS t kvs /\ length kvs = length kids /\ length KBS = length kids /\ kids_okv m kids kvs KBS
| Sarr kids =>
exists (a : Z) (ABS : list blk) (ps : list Z) (KBS : list (list blk)),
REST = (p, 48) :: ABS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb0 0 0 ++ [C8 (wz a)]) /\
alist segs fn m ABS a ps /\ length ps = length kids /\ length KBS = length kids /\ kids_okp m kids ps KBS
end.

#[using="Type"] Lemma jval_split : forall s m BS p rc,
jvalx s m BS p rc <-> exists pb0 PBS REST, BS = REST ++ PBS /\ opt_pbuf segs m PBS pb0 /\ jnode s m REST p rc pb0.
Proof.
intros s m BS p rc. destruct s as [|[|]| |[|]|kids|kids]; cbn; try reflexivity.
all: split; intros (pb0 & PBS & REST & E & O & H); exists pb0, PBS, REST; (split; [exact E|]); (split; [exact O|]); exact H.
Qed.

#[using="Type"] Lemma jnode_hdr : forall s m REST p rc pb0, jnode s m REST p rc pb0 ->
exists n ty udel ud cs rest, REST = (p, n) :: rest /\ 48 <= n /\
rw_cells m p ([C4 (wz ty); C4 (wz rc); C8 (wz (fn_ofF fn s)); C8 (wz pb0); C8 (wz udel); C8 (wz ud)] ++ cs).
Proof.
intros s m REST p rc pb0 J. destruct s as [|[|]| |[|]|kids|kids]; cbn in J.
- destruct J as (b & junk & -> & H). exists 48, JT_BOOLEAN, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & ud & udn & uds & -> & _ & H & _). exists 48, JT_DOUBLE, (fn_free_userdata fn), ud. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (bits & -> & _ & H). exists 48, JT_DOUBLE, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (cty & v & junk & -> & _ & H). exists 56, JT_INT, 0, 0. eexists. exists []. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & pd & pdn & str & junk2 & -> & _ & _ & _ & H & _). exists 56, JT_STRING, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (len & str & junk & -> & Hl & _ & H). exists (str_objsize len), JT_STRING, 0, 0. eexists. exists []. split; [reflexivity|]. split; [unfold str_objsize; lia|]. exact H.
- destruct J as (t & TBS & kvs & KBS & -> & H & _). exists 48, JT_OBJECT, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
- destruct J as (a & ABS & ps & KBS & -> & H & _). exists 48, JT_ARRAY, 0, 0. eexists. eexists. split; [reflexivity|]. split; [lia|]. exact H.
Qed.
End WithSegs.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition ser_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (pb lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word) (errv' : word) (buf' cap' bpos' : Z) (content' : list byte),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' ERRNO [C4 errv'] /\
HEAPx A' ((pb, PB_SZ) :: (buf', cap') :: LB) m' md' /\
pbuf_core rsegs m' pb buf' bpos' cap' content'.

Definition ser_spec (entry : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB REST : list blk) (p rc pb0 pb buf bpos cap lv fl lo : Z) (content : list byte) (errv : word),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
jnode rsegs S4F s m REST p rc pb0 -> incl REST LB -> lb_small LB ->
flags_ok fl -> 0 <= lv -> lv + sdepth s <= 1000 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ser_budget s ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m ERRNO [C4 errv] ->
tp = wz TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz p -> a1 = wz pb -> a2 = wz lv -> a3 = wz fl ->
(forall ms' md', ser_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz entry) fc None m (seg_rom rsegs)) md) T.

Definition SERVAL : Prop := forall s, ser_spec (fn_of s) s.
End Ser.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ESC_ENTRY : Z := 0x26fb4.
Definition ESC_LOOP : Z := 0x27084.
Definition MEMAPPEND : Z := 0x241a4.
Definition JHEX_SLOT : Z := 0x66a30.
Definition JHEX : Z := 0x12b12.
Definition ERRNO : Z := 490332.
Definition ESC_MASK : Z := 140754668238592.

Section Generic.

#[using="Type"] Lemma client_range_mono : forall LB1 LB2 SP SP' A k,
client_range S4L LB1 SP A k -> SP' <= SP -> (forall b, In b LB1 -> In b LB2) -> client_range S4L LB2 SP' A k.
Proof.
intros LB1 LB2 SP SP' A k [H|[H|(b & Hb & H1 & H2)]] HS HL; [left; lia | right; left; exact H | right; right].
exists b. split; [apply HL; exact Hb | split; assumption].
Qed.

#[using="Type"] Lemma client_range_sub : forall LBx SP A k A' k',
client_range S4L LBx SP A k -> A <= A' -> A' + k' <= A + k -> 0 <= k' -> client_range S4L LBx SP A' k'.
Proof.
intros LBx SP A k A' k' [H|[H|(b & Hb & H1 & H2)]] H3 H4 H5; [left; lia | right; left; intros a Ha; apply H; lia | right; right].
exists b. split; [exact Hb | lia].
Qed.

#[using="Type"] Lemma ro_bytes_sub : forall a bs i k,
ro_bytes rsegs a bs -> (i + k <= length bs)%nat -> ro_bytes rsegs (a + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
intros a bs. revert a. induction bs as [|b bs IH]; intros a i k H Hl.
- cbn in Hl. assert (i = 0%nat /\ k = 0%nat) as [-> ->] by lia. cbn. exact I.
- destruct H as [Hb Hbs]. destruct i as [|i].
+ cbn [skipn]. rewrite Z.add_0_r. destruct k as [|k]; [exact I|]. cbn. split; [exact Hb|].
pose proof (IH (a + 1) 0%nat k Hbs ltac:(cbn in Hl; lia)) as X. rewrite Z.add_0_r in X. exact X.
+ cbn [skipn]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IH; [exact Hbs | cbn in Hl; lia].
Qed.

#[using="Type"] Lemma src_cls_sub : forall LB n SP Sa src SP' i k,
src_cls LB n SP Sa src -> Z.of_nat (length src) = n -> SP' <= SP -> (i + k <= length src)%nat ->
src_cls LB (Z.of_nat k) SP' (Sa + Z.of_nat i) (firstn k (skipn i src)).
Proof.
intros LB n SP Sa src SP' i k SCL SRCL HS Hl. destruct SCL as [CR|RO].
- left. eapply client_range_sub; [eapply client_range_mono; [exact CR | exact HS | auto] | lia | lia | lia].
- right. apply ro_bytes_sub; assumption.
Qed.

#[using="Type"] Lemma bytes_at_sub : forall m Sa src i k,
bytes_at rsegs m Sa src -> (i + k <= length src)%nat -> bytes_at rsegs m (Sa + Z.of_nat i) (firstn k (skipn i src)).
Proof.
intros m Sa src i k (H0 & H1 & HB) Hl. split; [lia|]. split; [rewrite length_firstn, length_skipn; lia|].
intros j Hj. rewrite length_firstn, length_skipn in Hj.
replace (Sa + Z.of_nat i + Z.of_nat j) with (Sa + Z.of_nat (i + j)) by lia. rewrite (HB (i + j)%nat ltac:(lia)).
rewrite nth_error_firstn. replace (Nat.ltb j k) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn. reflexivity.
Qed.

End Generic.

Section Esc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.

Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb Sa n lo : Z) (src : list byte).
Let usp := bv_unsigned sp.

Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis SCL : src_cls LB n usp Sa src.
Hypothesis Hn : 0 < n < 2^31.
Hypothesis HSa : 0 <= Sa /\ Sa + n < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - 192 - 8320.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.

Definition escF (j1 j2 sb : list byte) : list cell :=
[CB 8 j1; C8 (wz 0x113f0); C8 (wz 0); C8 (wz JHEX_SLOT); CB 1 j2; CB 7 sb;
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition esc_mem (m : word -> option byte) (md : Model) : Prop :=
exists (A : AS S4L HIx) (buf cap bpos : Z) (content : list byte) (errv : word) (j1 j2 sb : list byte),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md /\
pbuf_core rsegs m pb buf bpos cap content /\
rw_cells rsegs m (usp + -144) (escF j1 j2 sb) /\
bytes_at rsegs m Sa src /\
rw_cells rsegs m ERRNO [C4 errv] /\
stk rsegs m lo (usp + -144) /\
heap_pres S4L LB usp m0 m /\ model_vm_only md0 md.

Definition esc_post (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word) (buf' cap' bpos' : Z) (content' : list byte) (errv' : word),
ret_statew S4L ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md0 md' /\
stk rsegs m' lo usp /\
heap_pres S4L LB usp m0 m' /\
rw_cells rsegs m' ERRNO [C4 errv'] /\
HEAPx A' ((pb, PB_SZ) :: (buf', cap') :: LB) m' md' /\
pbuf_core rsegs m' pb buf' bpos' cap' content' /\
bytes_at rsegs m' Sa src.

#[using="RC__ ra sp LB Sa n lo src usp SRCL SCL Hn HSa LO LOS"] Lemma esc_sa_pos : forall A bufx capx m md,
HEAPx A ((pb, PB_SZ) :: (bufx, capx) :: LB) m md -> 0 < Sa.
Proof.
intros A bufx capx m md HP.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
destruct SCL as [[CR|[CR|(b & Hb & H1 & H2)]]|RO].
- unfold usp in *. unfold_consts. lia.
- specialize (CR Sa ltac:(lia)). cbn [hl_client_static S4L] in CR. unfold s4_client_static in CR. lia.
- destruct b as [ba bn]. cbn in H1.
pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP ltac:(right; right; exact Hb)) as (_ & _ & Hba & _). lia.
- destruct src as [|b0 src']; [cbn in SRCL; lia|].
destruct RO as [[_ RAD] _]. apply ro_addr_range in RAD; lia.
Qed.

#[using="ra sp Sa n src usp HSa"] Lemma src_cls_sep_buf : forall A bufx capx m md k SP b sb,
HEAPx A ((pb, PB_SZ) :: (bufx, capx) :: LB) m md ->
src_cls LB k SP b sb -> Z.of_nat (length sb) = k -> 0 <= b -> b + k <= 2^64 -> alloc_ceiling <= SP ->
k = 0 \/ b + k <= bufx \/ bufx + capx <= b.
Proof.
intros A bufx capx m md k SP b sb HP SC L Hb Hbk HSP.
assert (HP' : HEAPx A ((bufx, capx) :: (pb, PB_SZ) :: LB) m md) by (eapply (heap_perm S4L HIx); [exact HP | apply perm_swap]).
eapply (src_cls_fresh_sep HIx _ ((pb, PB_SZ) :: LB)); [exact HP' | | exact L | exact Hb | exact Hbk | exact HSP].
destruct SC as [CR|RO]; [left | right; exact RO].
eapply client_range_mono; [exact CR | lia | intros bb Hbb; right; exact Hbb].
Qed.

#[using="ra n lo SRCL SCL Hn HSa LO LOS SPA"] Lemma src_pres_munch : forall A bufx capx m md m' W,
HEAPx A ((pb, PB_SZ) :: (bufx, capx) :: LB) m md -> bytes_at rsegs m Sa src -> munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= usp) \/ (bufx <= fst iv /\ snd iv <= bufx + capx)
\/ (pb <= fst iv /\ snd iv <= pb + PB_SZ)) W ->
bytes_at rsegs m' Sa src.
Proof.
intros A bufx capx m md m' W HP SRC MU HW.
pose proof (bv_unsigned_in_range 64 sp) as SPR.
assert (ASP : alloc_ceiling <= usp) by (unfold usp in *; unfold_consts; lia).
eapply (bytes_at_transport rsegs W); [exact SRC | exact MU |]. rewrite SRCL.
pose proof (src_cls_where _ _ _ _ _ SCL SRCL ltac:(lia) ltac:(lia) HIx _ _ _ _ HP ltac:(intros b Hb; right; right; exact Hb)) as W1.
pose proof (src_cls_sep_buf _ _ _ _ _ _ _ _ _ HP SCL SRCL ltac:(lia) ltac:(lia) ASP) as W2.
assert (HP' : HEAPx A ((bufx, capx) :: (pb, PB_SZ) :: LB) m md) by (eapply (heap_perm S4L HIx); [exact HP | apply perm_swap]).
assert (W3 : n = 0 \/ Sa + n <= pb \/ pb + PB_SZ <= Sa).
{ eapply (src_cls_fresh_sep HIx _ ((bufx, capx) :: LB)); [exact HP | | exact SRCL | lia | lia | exact ASP].
destruct SCL as [CR|RO]; [left | right; exact RO]. eapply client_range_mono; [exact CR | apply Z.le_refl | intros bb Hbb; right; exact Hbb]. }
clear HP' MU SRC. induction W as [|[l h] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn in H1. split; [| apply IH; exact HW].
lia.
Qed.

#[using="MEMMOVE n SRCL SCL HSa LO LOS SPA HT"] Lemma esc_append :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : Model) (T : TSet) (b k : Z) (sb : list byte),
esc_mem m md ->
bytes_at rsegs m b sb -> Z.of_nat (length sb) = k -> 0 < k < 2^31 -> 0 <= b -> b + k < 2^64 ->
src_cls LB k (usp + -144) b sb ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
esc_mem m' md' -> fsaved F F' -> frm0 fc' -> bytes_at rsegs m' b sb ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (Z_to_bv 64 (usp + -144)) gp (wz 0x77c00) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom rsegs)) md') T) ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (Z_to_bv 64 (usp + -144)) x3 (wz 0x77c00) t0 t1 t2 x8 x9 (wz pb) (wz b) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz MEMAPPEND) fcc None m (seg_rom rsegs)) md) T.
Proof.
intros until sb. intros INV SB SBL Hk Hb Hbk SBC -> Hret Hret2 FS FR K.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; unfold usp in *; unfold_consts; lia).
pose proof (src_cls_sep_buf _ _ _ _ _ _ _ _ _ HP SBC SBL Hb ltac:(lia) ltac:(unfold usp in *; unfold_consts; lia)) as SEP.
eapply (memappend_cps HIx MEMMOVE) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (n := k)
(lo := lo) (content := content) (src := sb) (errv := errv);
rewrite ?U2.
- exact HP.
- exact PB.
- lia.
- exact SB.
- exact SBL.
- exact SBC.
- exact Hb.
- exact Hbk.
- destruct SEP as [?|SEP]; [lia | exact SEP].
- exact ST.
- exact LO.
- lia.
- unfold usp in *. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 16 * 9) by lia. rewrite <- Zminus_mod_idemp_l, SPA. reflexivity.
- unfold usp in *. lia.
- exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- reflexivity.
- reflexivity.
- reflexivity.
-
intros ms' md' POST.
destruct POST as (m' & A' & r & errv' & buf' & cap' & RS & VM' & ST' & HPR' & ERR' & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
pose proof (heap_mem_inv _ _ _ _ _ _ HP') as MI'. cbn [hl_segs S4L] in MI'.
assert (SB' : bytes_at rsegs m' b sb).
{ eapply (src_cls_transport LB k (usp + -144) (usp + -144) LB); [exact SBC | exact SBL | exact SB | exact HPR' | lia | auto | exact MI' | lia | lia]. }
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FR) | exact SB'].

assert (PB' : exists bpos' content', pbuf_core rsegs m' pb buf' bpos' cap' content').
{ destruct OUT as [[_ PBF] | (_ & -> & -> & PBC)].
- destruct PBF as (bufq & bposq & sizeq & pre & post & E & L & C). injection E as <- <-. eauto.
- eauto. }
destruct PB' as (bpos' & content' & PB').
exists A', buf', cap', bpos', content', errv', j1, j2, sbf.
split; [exact HP'|]. split; [exact PB'|]. split; [| split; [| split; [exact ERR' | split; [exact ST' | split]]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPR' | exact FRc | left; lia].
+ eapply (src_cls_transport LB n usp (usp + -144) LB); [exact SCL | exact SRCL | exact SRC | exact HPR' | lia | auto | exact MI' | lia | lia].
+ eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | lia | auto]].
+ eapply model_vm_only_trans; [exact VM | exact VM'].
Qed.
End Esc.

End RC__1.
