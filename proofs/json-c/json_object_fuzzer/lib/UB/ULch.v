(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup UEQM Lib.GwApply QWxq Qfw3 QRjH QHnV QCcH QfLs Q0Ek QjDH UC8c Qsw7 QJjn UBpZ UT7i Uv6q U7zy UD4E UzWc Uuoa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0 Qfw3.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q U7zy UD4E.
Import UzWc.
Import Uuoa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ro_src : forall m a bs LB n SP,
mem_inv rsegs m -> ro_bytes_b rsegs a bs = true -> Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
bytes_at rsegs m a bs /\ src_cls LB n SP a bs.
Proof.
intros m a bs LB n SP MI RB L Ha Han. pose proof (ro_bytes_b_sound rsegs bs a RB) as RO.
split; [apply ro_bytes_at; [exact MI | lia | lia | exact RO] | right; exact RO].
Qed.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

#[using="Type"] Lemma cstr_slack : forall A LBx m md a n s,
HEAPx A LBx m md -> In (a, n) LBx -> cstr rsegs m a n s ->
exists slack, bytes_at rsegs m a (s ++ Z_to_bv 8 0 :: slack) /\
(- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) <= n - Z.of_nat (length s) - 1 + 15 /\
~ In (Z_to_bv 8 0) s.
Proof.
intros A LBx m md a n s HP Hin (L1 & NZ & junk & RW).
pose proof (heap_blk S4L HIx _ _ _ _ a n HP Hin) as (Hn & Hal & Ha0 & Hhi & _).
destruct (heap_blk_slack S4L HIx _ _ _ _ a n HP Hin) as (junk2 & BY2 & L2). cbn [hl_segs S4L] in BY2.
pose proof (rw_cells_bytes_at rsegs m a _ RW) as BY1. cbn [cells_bytes cbytes app] in BY1. rewrite app_nil_r in BY1.
destruct RW as [[WF _] _]. cbn in WF. destruct WF as [WF _]. rewrite !length_app in WF. cbn [length] in WF.
exists (junk ++ junk2). split; [| split].
- replace (s ++ Z_to_bv 8 0 :: junk ++ junk2) with ((s ++ Z_to_bv 8 0 :: junk) ++ junk2) by (rewrite <- app_assoc; reflexivity).
apply (proj2 (bytes_at_app rsegs m a _ _)). split; [exact BY1|].
rewrite length_app. cbn [length]. replace (a + Z.of_nat (length s + S (length junk))) with (a + n) by lia. exact BY2.
- rewrite length_app. Z.div_mod_to_equations. lia.
- intros Hin0. apply (proj1 (Forall_forall _ _) NZ _ Hin0). reflexivity.
Qed.

Hypothesis MEMMOVE : memmove_stmt.

Variables (sp gp : word) (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb lo : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hi_top S4L HIx.

Definition ser_mem (FA : Z) (FR : list cell) (m : word -> option byte) (md : Model) : Prop :=
exists (A : AS S4L HIx) (buf cap bpos : Z) (content : list byte) (errv : word),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md /\
pbuf_core rsegs m pb buf bpos cap content /\
rw_cells rsegs m FA FR /\
rw_cells rsegs m ERRNO [C4 errv] /\
stk rsegs m lo FA /\
heap_pres S4L LB usp m0 m /\ model_vm_only md0 md.

#[using="Type"] Lemma ser_mem_mem_inv : forall FA FR m md, ser_mem FA FR m md -> mem_inv rsegs m.
Proof. intros FA FR m md (A & buf & cap & bpos & content & errv & HP & _). pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. exact MI. Qed.
#[using="Type"] Lemma ser_mem_model_ok : forall FA FR m md, ser_mem FA FR m md -> model_ok md.
Proof. intros FA FR m md (A & buf & cap & bpos & content & errv & HP & _). exact (heap_model_ok _ _ _ _ _ _ HP). Qed.

#[using="Type"] Lemma ser_src_sep_buf : forall A bufx capx m md k SP b sb,
HEAPx A ((pb, PB_SZ) :: (bufx, capx) :: LB) m md ->
src_cls LB k SP b sb -> Z.of_nat (length sb) = k -> 0 <= b -> b + k <= 2^64 -> alloc_ceiling <= SP ->
k = 0 \/ b + k <= bufx \/ bufx + capx <= b.
Proof.
intros A bufx capx m md k SP b sb HP SC L Hb Hbk HSP.
assert (HP' : HEAPx A ((bufx, capx) :: (pb, PB_SZ) :: LB) m md) by (eapply (heap_perm S4L HIx); [exact HP | apply perm_swap]).
eapply (src_cls_fresh_sep HIx _ ((pb, PB_SZ) :: LB)); [exact HP' | | exact L | exact Hb | exact Hbk | exact HSP].
destruct SC as [CR|RO]; [left | right; exact RO].
destruct CR as [H|[H|(bb & Hbb & H1 & H2)]]; [left; exact H | right; left; exact H | right; right].
exists bb. split; [right; exact Hbb | split; assumption].
Qed.

#[using="Type"] Lemma ser_mem_pure : forall FA FR m md x,
ser_mem FA FR m md -> munch [] m x -> wmono rsegs m x -> mem_inv rsegs x -> ser_mem FA FR x md.
Proof.
intros FA FR m md x (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM) MU WM MI.
exists A, buf, cap, bpos, content, errv.
split. { eapply (heap_frame S4L HIx); [exact HP | intros a _ _ _; apply MU; exact I | exact WM | exact MI]. }
split. { destruct PB as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | exact I]). }
split; [eapply rw_cells_transport; [exact FRc | exact MU | exact WM | exact I]|].
split; [eapply rw_cells_transport; [exact ERR | exact MU | exact WM | exact I]|].
split; [eapply stk_transport; [exact ST | exact MU | exact WM | intros; left; exact I]|].
split; [| exact VM].
eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch S4L); [exact MU | exact WM | intros; exact I].
Qed.

#[using="MEMMOVE LO HT"] Lemma ser_append :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(FA : Z) (FR : list cell) (b k : Z) (sb : list byte),
ser_mem FA FR m md ->
bytes_at rsegs m b sb -> Z.of_nat (length sb) = k -> 0 <= k < 2^31 -> 0 <= b -> b + k < 2^64 ->
src_cls LB k FA b sb -> (0 < k \/ exists n', In (b, n') LB /\ 0 < n') ->
lo <= FA - 64 - 8256 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_mem FA FR m' md' -> fsaved F F' -> frm0 fc' -> bytes_at rsegs m' b sb ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) gp (wz TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom rsegs)) md') T) ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) x3 (wz TP) t0 t1 t2 x8 x9 (wz pb) (wz b) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz MEMAPPEND) fcc None m (seg_rom rsegs)) md) T.
Proof.
intros until sb. intros INV SB SBL Hk Hb Hbk SBC SEPX LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
pose proof (ser_src_sep_buf _ _ _ _ _ _ _ _ _ HP SBC SBL Hb ltac:(lia) ltac:(unfold_consts; lia)) as SEP.
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
- destruct SEP as [?|SEP]; [| exact SEP]. destruct SEPX as [?|(n' & Hin & Hn')]; [lia|].
pose proof (heap_blk S4L HIx _ _ _ _ b n' HP ltac:(right; right; exact Hin)) as (_ & _ & _ & Hbhi & _).
destruct (Z.eq_dec b buf) as [->|Hne].
+ exfalso. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn [map blk_addr fst] in ND.
inversion ND as [|x l Hni ND1]; subst. inversion ND1 as [|x2 l2 Hni2 ND2]; subst. apply Hni2. apply in_map_iff. exists (buf, n'). split; [reflexivity | exact Hin].
+ pose proof (heap_blk_disjoint S4L HIx _ _ _ _ b n' buf cap HP ltac:(right; right; exact Hin) ltac:(right; left; reflexivity) Hne). lia.
- exact ST.
- exact LO.
- lia.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' POST.
destruct POST as (m' & A' & r & errv' & buf' & cap' & RS & VM' & ST' & HPR' & ERR' & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
pose proof (heap_mem_inv _ _ _ _ _ _ HP') as MI'. cbn [hl_segs S4L] in MI'.
assert (SB' : bytes_at rsegs m' b sb).
{ eapply (src_cls_transport LB k FA FA LB); [exact SBC | exact SBL | exact SB | exact HPR' | lia | auto | exact MI' | lia | lia]. }
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM) | exact SB'].
assert (PB' : exists bpos' content', pbuf_core rsegs m' pb buf' bpos' cap' content').
{ destruct OUT as [[_ PBF] | (_ & -> & -> & PBC)].
- destruct PBF as (bufq & bposq & sizeq & pre & post & E & L & C). injection E as <- <-. eauto.
- eauto. }
destruct PB' as (bpos' & content' & PB').
exists A', buf', cap', bpos', content', errv'.
split; [exact HP'|]. split; [exact PB'|]. split; [| split; [exact ERR' | split; [exact ST' | split]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPR' | exact FRc | left; lia].
+ eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia | auto]].
+ eapply model_vm_only_trans; [exact VM | exact VM'].
Qed.

#[using="LO HT"] Lemma ser_memset :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 cv a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(FA : Z) (FR : list cell) (len : Z),
ser_mem FA FR m md ->
0 <= len < 2^31 ->
lo <= FA - 64 - 8256 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_mem FA FR m' md' -> fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) gp (wz TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom rsegs)) md') T) ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) x3 (wz TP) t0 t1 t2 x8 x9 (wz pb) (wz 18446744073709551615) cv (wz len) a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz PBMEMSET) fcc None m (seg_rom rsegs)) md) T.
Proof.
intros until len. intros INV Hlen LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
eapply (pbmemset_cps HIx) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (len := len)
(lo := lo) (content := content) (errv := errv);
rewrite ?U2.
- exact HP.
- exact PB.
- exact Hlen.
- exact ST.
- exact LO.
- lia.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- reflexivity.
- apply bv_eq. reflexivity.
- reflexivity.
- intros ms' md' POST.
destruct POST as (m' & A' & r & errv' & buf' & cap' & RS & VM' & ST' & HPR' & ERR' & HP' & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM)].
assert (PB' : exists bpos' content', pbuf_core rsegs m' pb buf' bpos' cap' content').
{ destruct OUT as [(_ & content' & PBC) | (_ & -> & -> & PBC)]; eauto. }
destruct PB' as (bpos' & content' & PB').
exists A', buf', cap', bpos', content', errv'.
split; [exact HP'|]. split; [exact PB'|]. split; [| split; [exact ERR' | split; [exact ST' | split]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPR' | exact FRc | left; lia].
+ eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia | auto]].
+ eapply model_vm_only_trans; [exact VM | exact VM'].
Qed.

#[using="LO HT"] Lemma ser_child :
forall (entry : Z) (s' : jshape), ser_spec HIx entry s' ->
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(FA : Z) (FR : list cell) (RESTc : list blk) (v rc' pbc lvc fl : Z),
ser_mem FA FR m md ->
jnode rsegs S4F s' m RESTc v rc' pbc -> incl RESTc LB -> lb_small LB -> flags_ok fl ->
0 <= lvc -> lvc + sdepth s' <= 1000 ->
lo <= FA - ser_budget s' -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_mem FA FR m' md' -> fsaved F F' -> frm0 fc' ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) gp (wz TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom rsegs)) md') T) ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) x3 (wz TP) t0 t1 t2 x8 x9 (wz v) (wz pb) (wz lvc) (wz fl) a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz entry) fcc None m (seg_rom rsegs)) md) T.
Proof.
intros entry s' SPEC. intros until fl. intros INV JN INCL LBS FL Hlv Hlvd LOS FAA FAU FA0 -> Hret Hret2 FS FRM K.
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
unfold ser_spec in SPEC.
eapply SPEC with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap) (lo := lo) (content := content) (errv := errv)
(REST := RESTc) (p := v) (rc := rc') (pb0 := pbc) (lv := lvc) (fl := fl);
rewrite ?U2.
- exact HP.
- exact PB.
- exact JN.
- exact INCL.
- exact LBS.
- exact FL.
- exact Hlv.
- exact Hlvd.
- exact ST.
- exact LO.
- exact LOS.
- exact FAA.
- unfold usp in *. lia.
- exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- intros ms' md' POST.
destruct POST as (m' & A' & r & errv' & buf' & cap' & bpos' & content' & RS & VM' & ST' & HPR' & ERR' & HP' & PB').
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM)].
exists A', buf', cap', bpos', content', errv'.
split; [exact HP'|]. split; [exact PB'|]. split; [| split; [exact ERR' | split; [exact ST' | split]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPR' | exact FRc | left; lia].
+ eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia | auto]].
+ eapply model_vm_only_trans; [exact VM | exact VM'].
Qed.
End Ser.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QId5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QId5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

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

Notation esc_memx := (esc_mem HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB pb Sa lo src).
Let esc_appendx := esc_append HIx MEMMOVE ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB pb Sa n lo src SRCL SCL HSa LO LOS SPA HT.
Notation esc_postx := (esc_post HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb Sa lo src).

#[using="MEMMOVE n SRCL SCL HSa LO LOS SPA HT"] Lemma esc_epilogue :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : Model) (T : TSet),
esc_memx m md -> fsaved F F' -> frm0 fc' ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -144)) gp (wz 0x77c00) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x272b0) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until T. intros INV FS FR K.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold usp in *. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold escF in FRc.
apply rz_evt; [exact MOK|].
symb_run 20%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold esc_post.
exists m, A. eexists. exists buf, cap, bpos, content, errv.
split; [| split; [exact VM | split; [| split; [exact HPR | split; [exact ERR | split; [exact HP | split; [exact PB | exact SRC]]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -144 + 144)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS | intros _; exact FR].
- release_frame FRc ST (bv_unsigned sp). exact ST.
Qed.

#[using="MEMMOVE SRCL SCL Hn HSa LO LOS SPA HT esc_appendx"] Lemma esc_exit :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : Model) (T : TSet) (start : Z),
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= n ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (usp + -144)) gp (wz 0x77c00) t0 t1 t2 (wz pb) (wz n) (wz start) a1 a2 a3 a4 a5 a6 a7
(wz Sa) x19 (wz (18446744073709551615 - Sa)) x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F' (wz 0x27298) fc' None m (seg_rom rsegs)) md) T.
Proof.
intros until start. intros INV FS FR Hst K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold usp in *. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold escF in FRc.
apply rz_evt; [exact MOK|].
destruct (Z.lt_ge_cases start n) as [LT|GE].
-
symb_run 8%nat [MEMAPPEND] [false; false].
try replace (start + Sa) with (Sa + start) by lia.
replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia.
replace (n - start) with (Z.of_nat (Z.to_nat (n - start))) by lia.
apply evt_RZ_done.
eapply esc_appendx with (sb := firstn (Z.to_nat (n - start)) (skipn (Z.to_nat start) src));
[ exact INV0 | | | lia | lia | lia | | reflexivity | lia | reflexivity | exact FS | exact FR | ].
+ apply bytes_at_sub; [exact SRC | lia].
+ rewrite length_firstn, length_skipn. lia.
+ apply (src_cls_sub LB n usp Sa src); [exact SCL | exact SRCL | lia | lia].
+ intros m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_epilogue; eassumption.
- symb_run 8%nat [0x272b0]%Z [true].
apply evt_RZ_done. eapply esc_epilogue; eassumption.
Qed.
End Esc.

End RC__1.
