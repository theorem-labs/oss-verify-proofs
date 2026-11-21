(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: decoded the encoded statements of hz_of_block_range, regions_alloc, regions_write, heap_block, know_blockwrite and other lemmas into plain Rocq, flattened Section SE lemmas, and replaced the literal 8388608 stack window with DRV_ZWIN in has_window; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Src0DrvLib.v, 85 lines within its lines 69-484. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare
SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 RefMemcpyLib
HeapIface DrvKit Js0MainEntry Js0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Decimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvLib.FPX_1.DrvLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2D0"]; ["2D1"; "2D2"; "2D4"; "2D5"; "2D6"; "2D7"; "2D8"; "2D9"; "2Nil"; "3False"; "3I"; "3True"; "3and"; "3eq"; "3ex"; "3not"]; ["4add"; "4of_num_uint"; "5UIntDecimal"; "6le"; "6lt"; "7map"; "8Z"; "0E"; "0E'"; "0HI"; "0K"; "0L"; "0LB"; "9store_ok"; ":mkCfg"; ";Model"]; [";VmMaps"; ";event"; ";m_halted"; ";m_vm_lazy"; ";m_vm_materialized"; ";m_vmmaps"; "<bvmap"; "0M"; "0M'"; "0R"; "0R'"; "=wbytes"; ">find_nz"; ">kentry_eqb"; ">kn_keep_g"; ">log_in_b"]; [">regions_ok"; "?block_range"; "?blocks_apart"; "?credit"; "?credit_ok"; "?debit"; "?defined"; "?hi_heap"; "?in_block"; "?lb_remove"; "?model_but_vm"; "?regs_preserved"; "?stack_ok"; "@CPm"; "@CPout"; "@CPstk"]; ["@CW"; "@IMG_W"; "@SCm"; "@has_window"; "@hz"; "@sub_block"; "AIMG_CLIENT"; "AIMG_RW"; "Ac_kept"; "Akeep_alloc"; "Akn_blk"; "Bgetr"; "Bmkst"; "Brdn"; "Bseg_rom"; "Csrealizes"]; ["Dwseg_ok"; "Ejunk_vals"; "Esr_after_call_j"; "FEVar"; "FEnv"; "FKWr"; "FSA"; "Fenv"; "Fexpr"; "Fkentry"; "Fridx"; "Fsentry"; "Gknow_ok"; "Gmem_denot"; "Gregs_ok"; "Hkn_vars_lt"]; ["Hsr_vars_lt"; "Hvals_ev"; "Iloaded_segments"; "JIn"; "Jexistsb"; "Jnth_error"; "Kadd"; "Kle"; "Klt"; "Kmodulo"; "Kof_nat"; "Kopp"; "Kpow"; "0VM"; "0a"; "0b"]; ["0bls"; "0bs"; "0cr"; "0ebs"; "0fx"; "0i"; "0k"; "0kn"; "0log"; "0m"; "0model"; "0model'"; "0n"; "0nb"; "0r"; "0ra"]; ["0scfg"; "0so"; "0sp0"; "0sr"; "LBV"; "LZ_to_bv"; "Lbv"; "Lbv_unsigned"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Record drv_layout (L : heap_layout) (sp0 : word) : Prop := DRV_LAYOUT {
dl_segs : hl_segs L = RSEGS;
dl_malloc : hl_malloc L = 0x9aab4;
dl_free : hl_free L = 0x9a974;
dl_tp : hl_tp L = 0xc7c60;
dl_img_lo : hl_img_lo L = 0x10000;
dl_img_hi : hl_img_hi L = 0xe9000;
dl_static : forall a, hl_alloc_static L a -> 0xe8068 <= a < 0xe8410;
dl_ro : forall a, hl_alloc_ro L a -> (0x10000 <= a < 0xb5000) \/ (0xe7ed0 <= a < 0xe7ed8) \/ (0xe7ef0 <= a < 0xe8068) \/ (0xe8410 <= a < 0xe8418) \/ (0xe8854 <= a < 0xe8858) \/ bv_unsigned sp0 <= a;
dl_errno : hl_errno L = 0xc7bbc;
dl_sptop : hl_sptop L = bv_unsigned sp0;
dl_stack : 0 <= hl_stack L <= 16384;
dl_k : 0 <= hl_k_per_malloc L;
dl_b : 0 <= hl_b_overhead L
}.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvLayout.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L scfg HI.
Variable sp0 : word.
Hypothesis Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Hypothesis DL : drv_layout L sp0.
Lemma wseg_5a000 : ltac2:(TCodec.tc2 tcn__Js0DrvLib "J'M'5&S0&SB&TEyR0+elP0%3221&Q1(Q2(A(B(C(E(D(H%211%411%611%811%:11%<11%>11%E3D@1(>%I3H21").
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_5f000 : OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim.wseg_ok Plain.M.loaded_segments (Z_to_bv 64 0xb5000) 212992 = true.
Proof. vm_compute. reflexivity. Qed.
Definition CPm (LB : list (Z * Z)) (sp : Z) (a : Z) : Prop := client_addr L LB sp (hl_stack L) a /\ ~ in_errno L a.
Definition SCm (sp : Z) (a : Z) : Prop := sp - hl_stack L <= a < sp.
Definition sub_block (LB : list (Z * Z)) (A nb : Z) : Prop :=
exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ block_range L A cap.
Definition hz (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0xe9000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.
Lemma hz_of_block_range : forall A n, block_range L A n -> hz A n.
Proof.
clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5). pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
pose proof (dl_sptop L sp0 DL) as TOP. unfold hz. rewrite IL, IH in B2. rewrite TOP in B5. repeat split; try lia.
Qed.
Lemma hz_sub : forall A n a m, hz A n -> A <= a -> 0 <= m -> a + m <= A + n -> hz a m.
Proof. clear Hsp Hal. intros A n a m (H1 & H2 & H3) Ha Hm Ham. unfold hz. lia. Qed.
Lemma sub_block_hz : forall LB A nb, sub_block LB A nb -> hz A nb.
Proof.
clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hz_of_block_range in HB. eapply hz_sub; [exact HB | lia | lia | lia].
Qed.
Lemma regions_alloc : forall vals ebs so bls vbnd LB,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
- 2 ^ 22 <= so <= 0 ->
(forall i nb, find_nz i bls = Some nb -> sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
(forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
(forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
regions_ok RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW E
(CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so)).
Proof.
intros vals ebs so bls vbnd LB.
intros E P0 Hso Hbl Hvb Hhi.
pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
pose proof (dl_errno L sp0 DL) as ER. pose proof (dl_sptop L sp0 DL) as TOP.
assert (NE : forall a, 0xc7bc0 <= a \/ a < 0xc7bbc -> ~ in_errno L a) by (intros a Ha; unfold in_errno; rewrite ER; lia).
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
- intros z Hz. destruct (Z.lt_ge_cases (bv_unsigned sp0 + z) (bv_unsigned sp0 + so - hl_stack L)) as [A|A].
+ left. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
+ right. unfold SCm. lia.
- intros i nb Hf. pose proof (sub_block_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|].
intros z Hz. unfold CPm, client_addr.
split; [left; exists (bv_unsigned (vals_ev vals i), cap); split; [exact Hin|]; cbn [fst snd]; lia | apply NE; lia].
- exact Hvb.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|].
intros z Hz. unfold CPm, client_addr. split; [right; left; rewrite TOP; lia | apply NE; lia].
- intros lo hi Hin. unfold IMG_CLIENT in Hin.
destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
intros a Ha; unfold CPm, client_addr; (split; [| apply NE; lia]); right; right; rewrite IL, IH; (split; [lia|]);
intros Hs; apply (dl_static L sp0 DL) in Hs; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xaf000) _ 24576%nat m 0xaf000 0xb5000);
[reflexivity | reflexivity | lia | exact wseg_5a000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb5000) _ 212992%nat m 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | exact wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma regs_preserved_kept : forall R R', regs_preserved R R' -> forall r : reg, In r c_kept -> getr R' r = getr R r.
Proof.
intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
Qed.
Lemma c_kept_no0 : ~ In (0%bv : reg) c_kept.
Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.
Lemma has_entry_nth : forall kn K, existsb (kentry_eqb K) kn = true -> exists i, nth_error kn i = Some K.
Proof.
intros kn K H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
apply In_nth_error in Hin. exact Hin.
Qed.
Lemma block_store_ok : forall vals ebs M kn v n (A : Z) (k : Z) (m : nat),
let E := Env (vals_ev vals) ebs in
know_ok RSEGS E M kn -> existsb (kentry_eqb (KWr (SA (EVar v) 0) n)) kn = true ->
vals_ev vals v = Z_to_bv 64 A -> (0 <= A)%Z -> (A < 2 ^ 64)%Z ->
(0 <= k)%Z -> (k + Z.of_nat m <= n)%Z ->
store_ok RSEGS M (Z_to_bv 64 (A + k)) m = true.
Proof.
intros vals ebs M kn v n A k m E HK Hhas Pv HA HAn Hk Hm.
destruct (has_entry_nth kn _ Hhas) as [i Hi].
pose proof (kwr_store_ok RSEGS E M kn i (EVar v) 0 n k m HK Hi Hk Hm) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite Pv in W. unfold v_addi in W.
rewrite u_small in W by lia. exact W.
Qed.
Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (- DRV_ZWIN)) DRV_ZWIN)) kn.
Lemma has_window_nth : forall kn, has_window kn = true -> exists i, nth_error kn i = Some (KWr (SA (EVar 0) (- DRV_ZWIN)) DRV_ZWIN).
Proof.
intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
apply In_nth_error in Hin. exact Hin.
Qed.
Lemma stack_ok_of_window : forall vals ebs M kn so,
let E := Env (vals_ev vals) ebs in
know_ok RSEGS E M kn -> has_window kn = true ->
vals_ev vals 0 = sp0 ->
- 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
stack_ok L M (bv_unsigned sp0 + so).
Proof.
intros vals ebs M kn so E HK Hw P0 Hso Hsoal. destruct (has_window_nth kn Hw) as [i Hn]. pose proof (dl_stack L sp0 DL) as ST.
pose proof Hsp as Hsp'. pose proof Hal as Hal'. pose proof (dl_sptop L sp0 DL) as TOP.
unfold stack_ok. rewrite TOP. split; [|split; [lia|split; [lia|split; [lia|]]]].
{ rewrite Z.add_mod, Hal, Hsoal by lia. reflexivity. }
intros d m Hd Hm.
pose proof (kwr_store_ok RSEGS E M kn i (EVar 0) (- DRV_ZWIN) DRV_ZWIN (so - hl_stack L + d) m HK Hn ltac:(lia) ltac:(lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W.
rewrite (dl_segs L sp0 DL).
replace (bv_unsigned sp0 + so - hl_stack L + d) with (bv_unsigned sp0 + (so - hl_stack L + d)) by lia. exact W.
Qed.
Lemma kn_blk_ok : forall vals ebs M' v n A,
let E := Env (vals_ev vals) ebs in
vals_ev vals v = Z_to_bv 64 A -> vals_ev vals 0 = sp0 ->
block_range L A n -> defined M' A n ->
know_ok RSEGS E M' (kn_blk v n).
Proof.
intros vals ebs M' v n A E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
assert (EA : bv_unsigned (edenot E (EVar v)) = A) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
unfold kn_blk, know_ok.
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
apply Forall_cons.
{ cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
destruct m as [|m']; [reflexivity|]. set (m := S m') in *.
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia.
specialize (Hdef (bv_unsigned x - A) ltac:(lia)). replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in Hdef by lia.
rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (M' x); [discriminate | exfalso; apply Hdef; reflexivity]. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
apply Forall_nil.
Qed.
Definition IMG_W : list (Z * Z) := [(0xb5000, 0xe7ed0); (0xe7ed8, 0xe7ef0); (0xe8428, 0xe8854); (0xe8858, 0xe9000)]%Z.
Definition CW (LB : list (Z * Z)) (a : Z) : Prop := ~ alloc_private L LB a.
Lemma regions_write : forall vals ebs bls LB,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
(forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W [] E (CW LB) (fun _ => True).
Proof.
intros vals ebs bls LB.
intros E P0 Hbl.
pose proof (dl_stack L sp0 DL) as ST. pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
pose proof (dl_sptop L sp0 DL) as TOP.
assert (RO := dl_ro L sp0 DL). assert (STA := dl_static L sp0 DL).
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CW, alloc_private. intros [[A _]|A]; [rewrite TOP in A; lia|].
apply RO in A. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi & HSB). pose proof (sub_block_hz _ _ _ HSB) as (Z1 & Z2 & Z3).
destruct HSB as (cap & Hnb & Hin & HB). pose proof (hz_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|]. intros z Hz. unfold CW, alloc_private. intros [[_ [A _]]|A].
+ apply A. exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
+ apply RO in A. lia.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. unfold IMG_W in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]);
intros a Ha; unfold CW, alloc_private; intros [[_ [_ A]]|A];
[ apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia
| apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia
| apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia
| apply A; rewrite IL, IH; split; [lia|]; intros Hs; apply STA in Hs; lia
| apply RO in A; lia ].
- intros lo hi [].
Qed.
Lemma heap_block : forall vals ebs bls LB cr M VM log,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
(forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_block LB (bv_unsigned (vals_ev vals i)) nb) ->
log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W log = true ->
hi_heap HI LB cr M VM -> hi_heap HI LB cr (mem_denot E M log) VM.
Proof.
intros vals ebs bls LB cr M VM log E P0 Hbl Hlog HH.
apply (hio_frame L scfg HI HIok LB cr M (mem_denot E M log) VM HH).
- intros a Ha Hp. apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W E (CW LB) (fun _ => True) []
(regions_write vals ebs bls LB P0 Hbl) M log a Hlog Ha).
unfold CW. tauto.
- intros x Hx. exact (mem_denot_grows E M log x Hx).
Qed.
Definition CPstk (a : Z) : Prop := a < 4096 \/ (0x10000 <= a < 0xe9000) \/ bv_unsigned sp0 - 8388608 <= a.
Lemma regions_stk : forall vals ebs,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W [] E CPstk (fun _ => True).
Proof.
intros vals ebs E P0.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPstk. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. discriminate.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. unfold IMG_W in Hin.
destruct Hin as [E1|[E1|[E1|[E1|[]]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPstk; lia.
- intros lo hi [].
Qed.
Lemma mem_heap_frame : forall vals ebs M log (a : Z),
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
hz a 1 ->
mem_denot E M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
intros vals ebs M log a E P0 Hlog (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W E CPstk (fun _ => True) [] (regions_stk vals ebs P0) M log a Hlog).
- lia.
- unfold CPstk. lia.
Qed.
Lemma rdn_heap_frame : forall vals ebs M log (a : Z) (n : nat),
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
hz a (Z.of_nat n) ->
rdn RSEGS (mem_denot E M log) (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
Proof.
intros vals ebs M log a n E P0 Hlog HZ. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
apply rdn_agree. intros j Hj. rewrite u_small by lia.
apply (mem_heap_frame vals ebs M log); [exact P0 | exact Hlog | eapply hz_sub; [exact HZ| lia | lia | lia]].
Qed.
Lemma heap_wbytes : forall LB cr M VM (A n a : Z) bs,
hi_heap HI LB cr M VM -> In (A, n) LB -> A <= a -> a + Z.of_nat (length bs) <= A + n -> A + n <= 2 ^ 64 ->
hi_heap HI LB cr (wbytes M (Z_to_bv 64 a) bs) VM.
Proof.
intros LB cr M VM A n a bs HH Hin H1 H2 H3.
destruct (hio_wf L scfg HI HIok LB cr M VM HH) as [WF _]. destruct (WF _ Hin) as (HBR & _ & _). cbn [fst snd] in *.
pose proof (hz_of_block_range _ _ HBR) as (Z1 & Z2 & Z3).
apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
- intros x Hx Hp. apply wbytes_out; [rewrite u_small by lia; lia|]. rewrite !u_small by lia.
destruct (Z.lt_ge_cases x a) as [Hlt|Hge]; [left; exact Hlt|]. right.
destruct (Z.lt_ge_cases x (a + Z.of_nat (length bs))) as [Hlt2|Hge2]; [|exact Hge2].
exfalso. destruct Hp as [[_ [Hnb _]]|Hro].
+ apply Hnb. exists (A, n). split; [exact Hin|]. cbn [fst snd]. lia.
+ apply (dl_ro L sp0 DL) in Hro. pose proof Hsp. lia.
- intros x Hx. exact (wbytes_grows bs M (Z_to_bv 64 a) x Hx).
Qed.
Definition CPout (A n : Z) (a : Z) : Prop := ~ (A <= a < A + n).
Lemma regions_blockwrite : forall vals ebs A n,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 -> hz A n ->
(forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
regions_ok RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False).
Proof.
intros vals ebs A n E P0 (Z1 & Z2 & Z3) Hhi. pose proof Hsp as Hsp'.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPout. lia.
- intros z Hz. exfalso. lia.
- intros i nb Hf. discriminate.
- intros v b Hf. discriminate.
- intros i Hi. destruct (Hhi i Hi) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. intros z Hz. unfold CPout. lia.
- intros lo hi Hin. unfold IMG_CLIENT in Hin.
destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPout; lia.
- intros lo hi Hin. unfold IMG_RW in Hin.
destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros Mx d m Hd Hm.
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xaf000) _ 24576%nat m 0xaf000 0xb5000);
[reflexivity | reflexivity | lia | exact wseg_5a000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
+ eapply (store_ok_window RSEGS Mx (Z_to_bv 64 0xb5000) _ 212992%nat m 0xb5000 0xe9000);
[reflexivity | reflexivity | lia | exact wseg_5f000 | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
Qed.
Lemma know_blockwrite : forall vals ebs M (A n a : Z) bs kn,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 -> hz A n -> A <= a -> a + Z.of_nat (length bs) <= A + n ->
(forall i, In i [3%nat; 4%nat] -> bv_unsigned sp0 <= bv_unsigned (vals_ev vals i) /\ bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64) ->
know_ok RSEGS E M kn ->
know_ok RSEGS E (wbytes M (Z_to_bv 64 a) bs) (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn).
Proof.
intros vals ebs M A n a bs kn E P0 HZ Ha Hbs Hhi HK. pose proof HZ as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
eapply (know_keep_g_sound RSEGS 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW E (CPout A n) (fun _ => False)
(regions_blockwrite vals ebs A n P0 HZ Hhi) M).
- intros x Hx Hout. unfold CPout in Hout. apply wbytes_out; rewrite ?u_small by lia; [lia|lia].
- intros x [].
- apply wbytes_grows.
- exact HK.
Qed.
Lemma vals_ev_junk : forall vals R' i, (i < 32)%nat ->
vals_ev (vals ++ junk_vals R') (length vals + i) = getr R' (Z_to_bv 5 (Z.of_nat i)).
Proof.
intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
Qed.
Lemma malloc_site : ltac2:(TCodec.tc2 tcn__Js0DrvLib "\D'8'TFyR0%211%411'9y8%611%811p041'S8%;11'S9%=11&QFy5%221=';%11;p0@1'Q?'='Q6%2211%H11&R3%52E4%K11'QA%M11!pYJ21'S7(S4&SAr?%211r>%5221&S>r1r<%33251&S<&SBr2%342159'M'5&S@&7rB%22QA1r@%5221(>%93821&S?rC%92QH1%3217%>3=16'Q3u5rD%?2QN1%4231rE(2%Q3221vTB%H3R421&SC(6u3u4(:%11R8%53R931%63R:51%83R;Q81'L&SG&TG%12RB>rH%QD21Q9%42RE1%6241&SF&SL+2+D%3221%5271+R0%6251%?231%A2:1p0C1pX<RO1&RC%11Q6%QH3QG1Q@&RK(TD(J%23RL@1%42Q<1&TE%E2JR9%22S=1%R13S=41&SK+F%I2H1%311%Q321RBz%Q52RD1%Q7231&SI+@%22R61%R=3S616rG+:%F3S@1E%H231%D2SOR>%RC3SO21&SH%12>R:+K%Q<2Q;1%QE2R=1%QG241&R4vQ;%231R8R;rJ+4%Q53SO1Q4%Q7231+hoS0%Q42T?1%S33T?31rK+1%Q<3T61Q;%Q>231%S83TD1F%R62Q2RN%F2ROQI%R9221%Q22RKR0%S=3T61Q6&R7vQ9rM&QErL%211%655@G41%TC1U1&QB%117(1%11U5%SJ3531%TE2U7U7%U;11&QCrN%211%S315%T13521&QDrO%211%S81UA%T63UA21%U51U0&QL%12T;I(3%12U4TB%T<3531&Q4r3rQ9%T=2UL1%4231&RErQ2%U1256%SA2V21%4331TH%SE261p0<1pXLUB1pX<V41rQ:%TI2V81%@2?1%U;23@%SK2V<1%SM21U2%SO241p0F1pX0UL1pYBV>1%T81UH%R911&4rQ=&S1r4%211%53VH41%UJ1UD%UL216%U<2VKUA&Q0rQ?%U?2VN1uQ0%4221%UE3VO61rQ@%UD2W31u:%9221%V72Q<1%SM2W8A%UL3W821&S2&Q5%W=1VO&S:&RH%443W<21rQA%V12W@1%83D31r8%V?3QI21&RJrQB%V72WF1%K21C%421QM&RIrQ8rQ7rQ6%44321Q0%Q;3WE61%VG4VFQ9=1(<r7%24W?W?1QKrQ<%UN3W@21&R5rQ;%23T01R0r9%S<1G%S@5S?6321&R:rQ>%2215&R1%13T87<&R2r:%231QNQE%V32XDW>%V52V31%WE1W;rQD%11W=%W<3X931p051pYJXJ1%V<2U8WF%TL2WGUO%V?221&R8rQC%221WFrA%UH2Y3S8%211rQF%113%WJ3XG31p071p0;1pWNXF1+RPP0%VL21X6+mTP0%U=2X81%W0231&O+mPS8%W221X7+mQP@%UC2X91%W6231%611+hnmL%W821SM+hnn0%UI2SO1%W<231%<11%X51RErQH%11RG%XC3Y@31p051p0<1p0D1pWNY@1'ROvT@(Q>&RLvT4%VO2Z:SE&RN%11Y2%554Q;3XJ1%721Y=%:4Y591R;p0<1p0Q71p0QG1p0R01p0R41p0R71p0R;1p0RG1p0S41p0S@1p0SH1tRBYMT01tYFZJT31p2Z91pXHZ<1pSBZ>1pSFZB1+cZeD%WG2[21rQ5%L5KS721HrQ4%O221%Q24YMQ11V8p081p0TF1p0TI1p0U41p0UI1p0UO1p0V71p0V>1p0VF1p0VI1p0VM1p0W31p0W;1p0W?1p0WF1p0WM1p0X21p0X;1p0XE1p0XI1p0YG1p0YM1p0Z31p0Z91p0ZD1p0ZI1tR@[4ZN1pRF[61pY0[@1pYH[<1pX2[=1pY4[C1pXJ[D1pX6[B1pRJ[D1pXF[I1pS@[K1pSD[O1pX@\31pY8\61pX8\91pYD\?1").
Proof.
intros vals ebs sr kn R M model LB cr n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
pose proof (hio_malloc L scfg HI HIok fx R M model LB cr n K) as MS.
rewrite (dl_segs L sp0 DL), (dl_malloc L sp0 DL), (dl_tp L sp0 DL) in MS.
rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
- intros R' M' model' A HA HP HBR HAP HDEF HPRES HBUT HH'.
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 A).
{ rewrite vals_ev_junk by lia. exact HA. }
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
{ rewrite vals_ev_app_l by lia. exact P0. }
apply (CONT R' M' model' A HL' HA').
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
+ apply Forall_app. split.
* eapply kn_blk_ok; [exact HA' | exact P0' | exact HBR | exact HDEF].
* unfold keep_alloc.
pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
destruct HPRES as (PR1 & PR2).
eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
(Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm LB (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
-- apply regions_alloc; try assumption.
++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
rewrite vals_ev_app_l by exact Hi32. exact H1.
++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
++ intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
-- intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
-- intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
-- exact HK1.
+ exact HH'.
+ exact HBUT.
+ exact HBR.
+ exact HAP.
+ intros x Hx. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
* pose proof (u64_range x). lia.
* unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hb. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
destruct Hb as (b & Hbin & Hr). destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
destruct (WF b Hbin) as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hs He. destruct HPRES as (PR1 & _). rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
* unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
Qed.
Lemma free_site : ltac2:(TCodec.tc2 tcn__Js0DrvLib "[J'8'TFyR0%211%411'9y8%611%811p041'S8%;11'S9%=11&QFy5%221=';%11;p0@1'Q?'='Q6%2211%H11&R3%52E4%K11'QA%M11!pYJ21'S7(S4&SAr@%211r?%5221&S>r1r=%33251&S<&SBr2%342159'M'5&S@&7rC%22QA1rA%5221(>%93821&S?rD%92QH1%3217%>3=16'Q3u5rE%?2QN1%4231rF(2%Q3221vTB%H3R421&SC(6u3u4(:%11R8%53R931%63R:51%83R;Q81'L&SG&TG%12RB>rI%QD21Q9%42RE1%6241&SF&SL+2+D%3221%5271+R0%6251%?231%A2:1p0C1pX<RO1&RC%11Q6%QH3QG1Q@&RK(TD(J%23RL@1%42Q<1&TEr>%F2K1%32S>1%R23S>51&SK+F%J2I1%311%Q421RAz%Q62RC1%Q8231&SI+@%22RI1%R>3S716(<rB%24S:S:R=1%QI3S:1R1+:%J3SD1I%L2Q?1%H2T3R;%RG3T321rJ+4%Q03SJ1O%Q2231+hoS0%O2T:1%RN3T:31rK+1%Q73T11Q6%Q9231%Q52T@RM%S43T@21%R22ME&SH%12GQF%R6231%N2S5QM%S:3T31Q2&R7vQ9rM&QErL%211%655BI41%T@1TN&QB%117(1%11U2%SG3531%TB2U4U4%U811&QCrN%211%S015%SN3521&QDrO%211%S51U>%T33U>21%U21TM&QL%12T8G(3%12U1T?%T93531&Q4r3rQ9%T:2UI1%4231&RE&R9rQ0rQ2%3221%U1289%SA2V21%7331TH%SE291p0?1pXLUB1pX<V41rQ:%TI2V81%C2B1%U;23C%SK2V<1%SM21U2%SO241p0I1pX0UL1pYBV>1%T81UH%T011&4rQ<&S1%11O%43VG31%UI1UC%UK215%U;2VJU@&Q0rQ>%U>2VM1uQ0%4221%UD3VN61&S2rQ=&Q5%W61VH&S:&RH%443W521rQ?%UJ2W91%93831r6%V83V221&RIrQ5rQ4rQ3%44321?%V:4V9QK71rQ8%QH21Q=r7%RL1;%S05RO3QO21&R:%12Q54%U:2WKVE%U<2U:1r;%11VCrQ@%11VE%VD3WA31p061pYJX21%UD2T?VN%SB2VOU7%UG221&R8%R;2Q5O%221VN%TO2X:RB%W411rQB%113%W13WN31p061p0:1pWNWM1+RPP0%V321W=+mTP0%T22W?1%V7231&O+mPS8%V921W>+mQP@%T82W@1%V=231%611+hnmL%V?21S7+hnn0%T>2S91%VC231%<11r4%UJ2Y51%X311rQD%113%WL3XI31p071p0>1p0F1pWNXI1'ROvT@(Q>&RLvT4%V82YCQOr<&RN%11X<%655X@431%821QKrQ7%<4X@;21p0>1p0Q;1p0QJ1p0R41p0R71p0R=1p0RD1p0S11tRBY5S91tYFZ2S<1pXHYC1pSBYE1pSFYI1rQ6+cZ[D%VO2Z:1%J5I31RLE%L21RL%O4Y3N1V1p071p0SL1p0SO1p0T:1p0U21p0U81p0U@1p0UG1p0UO1p0V21p0V71p0V>1p0VF1p0VL1p0W11p0W61p0W?1p0WJ1p0WN1p0XL1p0Y21p0Y81p0Y>1p0YI1p0YN1tR@Z9Z31pRFZ;1pY0ZE1pYHZA1pX2ZB1pY4ZH1pXJZI1p2ZJ1pX6ZH1pRJZJ1pXFZO1pS@[11pSD[51pX@[91pY8[<1pX8[?1pYD[E1").
Proof.
intros vals ebs sr kn R M model LB cr A n so bls vbnd ra K E HR HK Hsv Hkv HL5 P0 Hhi Hiw
R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 HH Hh Hlz Hmt Hbl Hvb HK0 CONT.
pose proof (hio_free L scfg HI HIok fx R M model LB cr A n K) as MS.
rewrite (dl_segs L sp0 DL), (dl_free L sp0 DL), (dl_tp L sp0 DL) in MS.
rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia. eapply stack_ok_of_window; eassumption.
- intros R' M' model' HP HPRES HBUT HH'.
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0).
{ rewrite vals_ev_app_l by lia. exact P0. }
apply (CONT R' M' model' HL').
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_kept R R' HP) c_kept_no0).
+ unfold keep_alloc.
pose proof (env_app_know RSEGS vals (junk_vals R') ebs M kn Hkv HK) as HK1.
destruct HPRES as [[PR1 PR2] _].
eapply (know_keep_sound RSEGS 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW
(Env (vals_ev (vals ++ junk_vals R')) ebs) (CPm (lb_remove A LB) (bv_unsigned sp0 + so)) (SCm (bv_unsigned sp0 + so))).
* apply regions_alloc; try assumption.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1).
rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros i Hi. rewrite vals_ev_app_l; [apply Hhi; exact Hi|]. destruct Hi as [<-|[<-|[]]]; lia.
* intros a Ha [HC HE]. rewrite R2, u_small in PR1 by lia. apply PR1; assumption.
* intros a HS. rewrite R2, u_small in PR2 by lia. apply PR2. exact HS.
* exact HK1.
+ exact HH'.
+ exact HBUT.
+ intros x Hx. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PR1.
* pose proof (u64_range x). lia.
* unfold client_addr. right. left. rewrite (dl_sptop L sp0 DL).
pose proof (u64_range x). pose proof (dl_stack L sp0 DL). lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hb. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [exact Ha | left; exact Hb |].
destruct Hb as (b & Hbin & Hr).
assert (Hbin' : In b LB).
{ clear -Hbin. induction LB as [|c LB' IH]; [destruct Hbin|]. cbn [lb_remove] in Hbin.
destruct (Z.eqb (fst c) A); [right; exact Hbin|]. destruct Hbin as [<-|Hbin]; [left; reflexivity | right; apply IH; exact Hbin]. }
destruct (hio_wf L scfg HI HIok LB cr M (m_vmmaps model) HH) as [WF _].
destruct (WF b Hbin') as (HBRb & _ & _). pose proof (hz_of_block_range _ _ HBRb) as (Y1 & Y2 & Y3).
unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
+ intros a Ha Hs He. destruct HPRES as [[PR1 _] _]. rewrite R2, u_small in PR1 by lia. apply PR1; [lia | |].
* unfold client_addr. right. right. rewrite (dl_img_lo L sp0 DL), (dl_img_hi L sp0 DL). split; [lia|].
intros Hst. apply (dl_static L sp0 DL) in Hst. lia.
* unfold in_errno. rewrite (dl_errno L sp0 DL). lia.
Qed.
End DrvLayout.
End FPX_1.
