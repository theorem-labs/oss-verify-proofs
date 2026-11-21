(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: writes out the encoded Jb0DrvLib statements and SE section lemmas as plain lemmas, narrows the stack window to 6144513 bytes, and adds a channel-reader field di_rdr with sbm_rdrA, model_rt_rdr, with_fds_rdr threaded through dinv_frame and dinv_model; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0DrvLib.v, 151 lines within its lines 22-853. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Decimal."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Number."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvNodesLazyK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvLib.FPX_1.DrvLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0Ad"; "0As"; "1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"]; ["1pair"; "1prod"; "1true"; "2D3"; "2D5"; "2D6"; "2Nil"; "3I"; "3True"; "3and"; "3eq"; "3ex"; "3not"; "3or"; "4add"; "4of_num_uint"]; ["5UIntDecimal"; "6le"; "6lt"; "7map"; "7nth"; "8Z"; "0E"; "0E'"; "0FF"; "0FF'"; "0H"; "0HI"; "0K"; "0L"; "0LB"; "0LB'"]; ["0LBc"; "0LK"; "0LK'"; "9Fs"; ":store_ok"; ";mkCfg"; "<FdEntry"; "<Model"; "<VmState"; "<event"; "<m_fds"; "<m_fs"; "<m_halted"; "<m_vm"; "<m_vm_lazy"; "<with_fds"]; ["=bvmap"; "0M"; "0M'"; "0MV"; "0Mx"; "0P"; "0R"; "0R'"; ">lzinv"; "?MInv"; "?mrestrict"; "?same_but_materialized"; "?segs_below_b"; "@find_nz"; "@log_in_b"; "@regions_ok"]; ["Anolazy_rng"; "Bblocks_apart"; "Bcredit"; "Bdefined"; "Bin_block"; "Blb_remove"; "Bregs_preserved"; "CS"; "Caacc"; "Cablock_range"; "Caclient"; "Cacredit_ok"; "Cadebit"; "Cahid"; "Capp_rng"; "Car_sptop"]; ["Car_stack_top"; "Cart_private"; "Castack_ok"; "Cblock_shadow"; "Cfframe"; "Cin_shadow_of"; "Cmodel_rt"; "Cri_inv"; "Cshadow_blk"; "Cvml"; "Cvml_of"; "DCPa"; "DCWA"; "DSCa"; "DSTKTOP"; "Ddinv"]; ["Dhas_window"; "DhzA"; "Dsub_blockA"; "EIMG_CLIENT_A"; "EIMG_RW_A"; "EIMG_W_A"; "Ec_kept"; "Ekeep_allocA"; "Ekn_blkA"; "Fgetr"; "Fmkst"; "Frdn"; "Fseg_rom"; "Gsrealizes"; "Hwseg_ok"; "Ijunk_vals"]; ["Isr_after_call_j"; "JEVar"; "JEnv"; "JKWr"; "JSA"; "Jenv"; "Jexpr"; "Jkentry"; "Jridx"; "Jsentry"; "Kknow_ok"; "Kmem_denot"; "Kregs_ok"; "Lkn_vars_lt"; "Lsr_vars_lt"; "Lvals_ev"]; ["Mloaded_segments"; "NIn"; "Nincl"; "Nnth_error"; "Oadd"; "Ole"; "Olt"; "Omodulo"; "Oof_nat"; "Oopp"; "Opow"; "Osub"; "Oto_nat"; "0V"; "0a"; "0ar"]; ["0b"; "0bls"; "0bs"; "0cap"; "0capd"; "0caps"; "0cr"; "0cr'"; "0dst"; "0ebs"; "0f"; "0fx"; "0hi"; "0hi'"; "0i"; "0j"]; ["0k"; "0kn"; "0lo"; "0lo'"; "0log"; "0m"; "0m'"; "0model"; "0model'"; "0n"; "0nb"; "0p"; "0r"; "0ra"; "0scfg"; "0scr"]; ["0scr'"; "0so"; "0sp"; "0sp0"; "0sr"; "0src"; "PBV"; "PZ_to_bv"; "Pbv"; "Pbv_unsigned"; "0u"; "0v"; "0vals"; "0vals'"; "0vbnd"; "0x"]; ["0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma no_bls : forall (P : nat -> Z -> Prop) i nb, DrvKitA.find_nz i [] = Some nb -> P i nb.
Proof. intros P i nb H. discriminate H. Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvLayoutA.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
Record drv_layoutA : Prop := DLA {
dla_segs : hl_segs L = ASEGS;
dla_malloc : hl_malloc L = 0x79190; dla_free : hl_free L = 0x7918c; dla_memcpy : icl_memcpy IL = 0x77608;
dla_tp : hl_tp L = 0x670ac0;
dla_img_lo : hl_img_lo L = 0x10000; dla_img_hi : hl_img_hi L = 0x693000;
dla_sptop : ar_sptop ar = bv_unsigned sp0;
dla_scr : 0 <= hl_scr_malloc L <= 4096 /\ 0 <= hl_scr_free L <= 4096 /\ 0 <= hl_scr_mem L <= 4096;
dla_client : forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> ~ hl_rt_static L a;
dla_ro : forall lo hi a, In (lo, hi) IMG_W_A -> lo <= a < hi -> ~ hl_rt_ro L a;
dla_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x693000
}.
Hypothesis DL : drv_layoutA.
Lemma wseg_stage : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "H'J'8&SN&T@&V7yR0+V[lT@%3221&O(Q0(E(D(C(F%411%311%511%611%811%:11%<11%C3B>1(B%G3F21").
Proof. vm_compute. reflexivity. Qed.
Lemma vis_of_inv : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "R:'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG&S7vQ;r8r7r6r5r4r3&S:r2%211%;8:9876541'I&TEz%2216&TF&TJ+2+R0%3221%52<1%:271'M+Vb\P0%92B1&TK&V9vV3%22Q51+XPPP0%5221%C21I&RDr:%221L%=241%>2<1'J'8&RM&V7%12QBQ4%33Q8Q61(:%73621p091p0I1p0Q51pYNR01p[@QC1pT4QE1p2R11pZ>QO1pS4R11pRBR21pRNR51").
Proof.
intros LB FF LK cr A M model a HH Ha Hc.
destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [exfalso | reflexivity].
unfold ahid, mkH in Hh. apply andb_prop in Hh as [Hl _].
destruct (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
specialize (LZ (Z_to_bv 64 a) Hl). cbv zeta in LZ. rewrite u_small in LZ by lia.
rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
destruct Hc as [Hc|[Hc|Hc]]; [lia | lia | exact (Z3 Hc)].
Qed.
Lemma nolazy_of_inv : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "RA'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051'QG&S7vQ;r9r8r7r6r5r4&S:r3%211%;8:9876541&TE&TD&V9%12G6r2%4221&TJ+2+R0%3221%:251'Izr1%>221&TF%123E%6231'M%A2Q7J%C21@+Vb\P0%7221&TKvV3%G2Q=1+XPPP0%4221%L218&RDr=%221;%>241%?2;1p0A1p[2QN1&R@&QN%11Q=%331Q=Q<p051p0O1p0Q;1p[DR61pYNQO1p[@QJ1pT4QL1p2R81pZ>R61pS4R81pRBR91pRNR<1").
Proof.
intros LB FF LK cr A M model a n HH Hn Hc k Hk. pose proof (u64_range a) as Ua.
destruct (page_in_ranges (page_base_of (bv_unsigned a + k)) (m_vm_lazy model)) eqn:Hp; [exfalso | reflexivity].
destruct (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
specialize (LZ (Z_to_bv 64 (bv_unsigned a + k))). unfold page_base in LZ. rewrite u_small in LZ by lia.
specialize (LZ Hp). cbv zeta in LZ. rewrite (dla_img_hi DL), (dla_sptop DL) in LZ. destruct LZ as (Z1 & Z2 & Z3 & _).
destruct (Hc k Hk) as [H1|[H1|H1]]; [lia | lia | exact (Z3 H1)].
Qed.
Definition CPa (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (H H' : word -> bool) (a : Z) : Prop :=
aclient L ar LB FF sp scr a /\ H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false.
Definition SCa (sp scr : Z) (a : Z) : Prop := sp - scr <= a < sp.
Definition sub_blockA (LB : list (Z * Z)) (A nb : Z) : Prop :=
exists cap, 0 < nb <= cap /\ In (A, cap) LB /\ ablock_range L ar A cap.
Definition hzA (A n : Z) : Prop := 4096 <= A /\ (A + n <= 0x10000 \/ 0x693000 <= A) /\ A + n <= bv_unsigned sp0 - 8388608.
Lemma hzA_of_block_range : forall A n, ablock_range L ar A n -> hzA A n.
Proof.
clear Hsp Hal. intros A n (B1 & B2 & B3 & B4 & B5 & B6). rewrite (dla_img_lo DL), (dla_img_hi DL) in B2. rewrite (dla_sptop DL) in B5.
unfold hzA. repeat split; lia.
Qed.
Lemma sub_blockA_hz : forall LB A nb, sub_blockA LB A nb -> hzA A nb.
Proof. clear Hsp Hal. intros LB A nb (cap & Hnb & _ & HB). apply hzA_of_block_range in HB. unfold hzA in *. lia. Qed.
Lemma regions_callA : forall vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model',
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
- 2 ^ 22 <= so <= 0 -> 0 <= scr <= 4096 ->
ri_inv HI LB FF LK cr A M (vml_of model) -> ri_inv HI LB' FF' LK' cr' A' M' (vml_of model') ->
(forall a, in_block LBc a -> in_block LB a) -> (forall a, in_block LBc a -> in_block LB' a) ->
(forall i nb, find_nz i bls = Some nb -> sub_blockA LBc (bv_unsigned (vals_ev vals i)) nb) ->
(forall v b, find_nz v vbnd = Some b -> bv_unsigned (vals_ev vals v) <= b) ->
regions_ok ASEGS 0 so scr bls vbnd [] IMG_CLIENT_A IMG_RW_A E
(CPa LBc FF (bv_unsigned sp0 + so) scr (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) scr).
Proof.
intros vals ebs so scr bls vbnd LBc LB LB' FF FF' LK LK' cr cr' A A' M M' model model' E P0 Hso Hscr HH HH' Hsub Hsub' Hbl Hvb.
pose proof Hsp as Hsp'.
assert (VIS : forall a, 0 <= a < 2 ^ 64 -> (a < 0x693000 \/ bv_unsigned sp0 - 8388608 <= a \/ in_block LBc a) ->
ahid A model (Z_to_bv 64 a) = false /\ ahid A' model' (Z_to_bv 64 a) = false).
{ intros a Ha Hc. split.
- apply (vis_of_inv _ _ _ _ _ _ _ a HH Ha). destruct Hc as [Hc|[Hc|Hc]]; auto.
- apply (vis_of_inv _ _ _ _ _ _ _ a HH' Ha). destruct Hc as [Hc|[Hc|Hc]]; auto. }
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CPa. split; [|apply VIS; lia].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
- intros z Hz. right. unfold SCa. lia.
- intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). pose proof (hzA_of_block_range _ _ HB) as (Y1 & Y2 & Y3).
split; [lia|]. intros z Hz.
assert (IB : in_block LBc (bv_unsigned (vals_ev vals i) + z)).
{ exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia. }
unfold CPa. split; [left; exact IB | apply VIS; [lia | right; right; exact IB]].
- exact Hvb.
- intros i [].
- intros lo hi Hin. pose proof (dla_client DL lo hi) as NS. destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3).
split; [lia|]. split; [lia|]. intros a Ha. unfold CPa. split; [|apply VIS; lia]. unfold aclient. right. right. left.
rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. exact (NS a Hin Ha).
- intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
intros Mx d m Hd Hm.
apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x65f090) (Z_to_bv 64 d) 65536%nat m 0x65f090 0x66f090);
first [exact wseg_stage | reflexivity | lia | (rewrite u_small by lia; lia)].
Qed.
Lemma regs_preserved_keptA : forall R R', regs_preserved R R' -> forall r : reg, In r c_kept -> getr R' r = getr R r.
Proof.
intros R R' HP r Hr. apply HP. unfold c_kept in Hr. unfold callee_saved_idx.
repeat (destruct Hr as [<-|Hr]; [cbn; tauto|]). destruct Hr.
Qed.
Lemma c_kept_no0A : ~ In (0%bv : reg) c_kept.
Proof. unfold c_kept. intros H. repeat (destruct H as [H|H]; [discriminate|]). exact H. Qed.
Lemma vals_ev_junkA : forall vals R' i, (i < 32)%nat ->
vals_ev (vals ++ junk_vals R') (length vals + i) = getr R' (Z_to_bv 5 (Z.of_nat i)).
Proof.
intros vals R' i Hi. rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hi. reflexivity.
Qed.
Lemma aclient_scr_mono : forall LB FF sp scr scr' a, 0 <= scr' <= scr -> aclient L ar LB FF sp scr a -> aclient L ar LB FF sp scr' a.
Proof.
intros LB FF sp scr scr' a Hs Hc. unfold aclient, aclient_g in *.
destruct Hc as [Hc|[Hc|Hc]]; [left; exact Hc | right; left; split; [tauto | lia] | right; right; exact Hc].
Qed.
Definition has_window (kn : list kentry) : bool := existsb (kentry_eqb (KWr (SA (EVar 0) (-6144513)) (6144513))) kn.
Lemma has_window_nth : forall kn, has_window kn = true -> exists i, nth_error kn i = Some (KWr (SA (EVar 0) (-6144513)) (6144513)).
Proof.
intros kn H. unfold has_window in H. apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
apply In_nth_error in Hin. exact Hin.
Qed.
Lemma window_store_ok : forall vals ebs MV kn (z : Z) (m : nat),
let E := Env (vals_ev vals) ebs in
know_ok ASEGS E MV kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
- 6144513 <= z -> z + Z.of_nat m <= 0 ->
store_ok ASEGS MV (Z_to_bv 64 (bv_unsigned sp0 + z)) m = true.
Proof.
intros vals ebs MV kn z m E HK Hw P0 Hz Hm. destruct (has_window_nth kn Hw) as [i Hn].
pose proof (kwr_store_ok ASEGS E MV kn i (EVar 0) (-6144513) 6144513 z m HK Hn ltac:(lia) ltac:(lia)) as W.
unfold adenot in W. cbn [a_base a_off edenot ev E] in W. rewrite P0 in W. unfold v_addi in W. exact W.
Qed.
Lemma segs_belowA : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "8'J'8&R<&T@+Vb\P0%3221(B%73621").
Proof. vm_compute. reflexivity. Qed.
Lemma store_ok_defined : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "Q='V8yR0%211'?y8%511%311p051'Q5'I&TE+Vb\P0r1%3221&TF&TJ+2+R0%3221%5271%;271'J'8&QD&T@r3&V7r2%22K1u1%746521(B%;3:21&Lr4%92Q2:%211(4%11Q1%B3Q131%711p091p0F1pYNQ31pT:Q51").
Proof.
intros Mx a Ha Hs. cbn [store_ok] in Hs. unfold wview in Hs.
destruct (Mx (Z_to_bv 64 a)) as [b|]; [discriminate|]. exfalso.
rewrite (find_segment1_none_above ASEGS 0x693000 (bv_unsigned (Z_to_bv 64 a)) segs_belowA) in Hs by (rewrite u_small by lia; lia). discriminate.
Qed.
Lemma window_defined : forall vals ebs (H : word -> bool) M kn,
let E := Env (vals_ev vals) ebs in
know_ok ASEGS E (mrestrict H M) kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
forall a, bv_unsigned sp0 - 6144513 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None.
Proof.
intros vals ebs H M kn E HK Hw P0 a Ha. pose proof Hsp as Hsp'.
pose proof (window_store_ok vals ebs _ kn (a - bv_unsigned sp0) 1 HK Hw P0 ltac:(lia) ltac:(lia)) as W.
replace (bv_unsigned sp0 + (a - bv_unsigned sp0)) with a in W by ring.
apply (store_ok_of_mrestrict ASEGS) in W. apply store_ok_defined; [lia | exact W].
Qed.
Lemma astack_ok_of_window : forall vals ebs (H : word -> bool) M kn so scr LB FF LK cr A V,
let E := Env (vals_ev vals) ebs in
know_ok ASEGS E (mrestrict H M) kn -> has_window kn = true -> vals_ev vals 0 = sp0 ->
- 2 ^ 22 <= so <= 0 -> so mod 16 = 0 -> 0 <= scr <= 4096 ->
ri_inv HI LB FF LK cr A M V ->
defined M (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0) ->
astack_ok L ar M scr (bv_unsigned sp0 + so).
Proof.
intros vals ebs H M kn so scr LB FF LK cr A V E HK Hw P0 Hso Hsoal Hscr HH Hdef. pose proof Hsp as Hsp'. pose proof Hal as Hal'.
unfold astack_ok. rewrite (dla_sptop DL), (dla_segs DL).
split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros d m Hd Hm. apply (store_ok_of_mrestrict ASEGS H).
replace (bv_unsigned sp0 + so - scr + d) with (bv_unsigned sp0 + (so - scr + d)) by ring.
apply (window_store_ok vals ebs _ kn _ m HK Hw P0); lia.
- intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlt|Hge].
+ apply (window_defined vals ebs H M kn HK Hw P0). lia.
+ replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
Qed.
Lemma kn_blkA_ok : forall vals ebs Mx v n u,
let E := Env (vals_ev vals) ebs in
vals_ev vals v = Z_to_bv 64 u -> vals_ev vals 0 = sp0 ->
ablock_range L ar u n -> defined Mx u n ->
know_ok ASEGS E Mx (kn_blkA v n).
Proof.
intros vals ebs Mx v n u E Pv P0 HBR Hdef. pose proof HBR as (_ & _ & B2 & B3 & _).
pose proof (hzA_of_block_range _ _ HBR) as (Z1 & Z2 & Z3). pose proof Hsp as Hsp'.
assert (EA : bv_unsigned (edenot E (EVar v)) = u) by (cbn [edenot ev E]; rewrite Pv; apply u_small; lia).
unfold kn_blkA, know_ok.
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. lia. }
apply Forall_cons. { cbn [kentry_ok]. rewrite EA. split; [lia | exact B2]. }
apply Forall_cons.
{ cbn [kentry_ok]. split. { unfold flat, estart. cbn [a_base a_off]. rewrite EA. lia. }
intros d m Hd Hm. unfold estart. cbn [a_base a_off]. rewrite EA.
destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia.
specialize (Hdef (bv_unsigned x - u) ltac:(lia)). replace (u + (bv_unsigned x - u)) with (bv_unsigned x) in Hdef by lia.
rewrite Z_to_bv_bv_unsigned in Hdef. unfold wview. destruct (Mx x); [discriminate | exfalso; apply Hdef; reflexivity]. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E]. rewrite P0.
change (ev E v) with (vals_ev vals v). rewrite Pv, u_small by lia. right. lia. }
apply Forall_cons. { cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot ev E].
change (ev E v) with (vals_ev vals v). rewrite Pv, !u_small by lia. lia. }
apply Forall_nil.
Qed.
Lemma lzinv_of_inv : forall LB FF LK cr A M model,
ri_inv HI LB FF LK cr A M (vml_of model) -> MInv A model -> m_halted model = None ->
lzinv ASEGS (ahid A model) A model.
Proof.
intros LB FF LK cr A M model HH HM Hh.
destruct (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
unfold lzinv. split.
{ intros a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hl _].
apply (find_segment1_none_above ASEGS 0x693000 _ segs_belowA).
pose proof (LZ a Hl) as (Z1 & _). cbv zeta in Z1. rewrite (dla_img_hi DL) in Z1. exact Z1. }
split; [unfold ahid; apply lazy_cover_mkH; intros r Hr; exact Hr|].
split; [exact AWF|]. split; [exact HM | exact Hh].
Qed.
Lemma model_rt_halted : forall m m', model_rt m m' -> m_halted m' = m_halted m.
Proof. intros m m' ->. destruct m; reflexivity. Qed.
Definition CWA (LB : list (Z * Z)) (a : Z) : Prop :=
in_block LB a \/ bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).
Lemma img_w_client : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "Q2'Q5&TA'A%1233(@r2r1%347721&SE%83621'K'I&SC%<3:61&TEr5%22;1r4%421<+RPP0%6215+Vb\P0%8251%<231%=261%>291%?2=1qZLK1%B2L1q[8M1%D2N1p0F1pZJQ01p[6Q11").
Proof.
intros lo hi Hin. destruct (img_w_sub lo hi Hin) as (lo' & hi' & Hin' & H1 & H2). destruct (img_client_rng lo' hi' Hin') as (I1 & I2 & I3).
exists lo', hi'. split; [exact Hin'|]. split; [exact H1|]. split; [exact H2|].
unfold IMG_W_A in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma cwa_not_bshadow : forall LB FF LK cr A M V a, ri_inv HI LB FF LK cr A M V -> CWA LB a -> ~ block_shadow LB a.
Proof.
intros LB FF LK cr A M V a.
intros HH HC (b' & Hb' & X').
pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB b' Hb') as ((Q0 & _ & Q16 & Q3 & Q4 & Q5) & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
unfold in_shadow_of, S, SB in X'. rewrite (dla_sptop DL) in Q4. pose proof Hsp as HSP.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
- destruct HB as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
- lia.
- destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma cwa_not_private : forall LB FF LK cr A M V a, ri_inv HI LB FF LK cr A M V -> 0 <= a < 2 ^ 64 -> CWA LB a -> ~ art_private L ar LB FF a.
Proof.
intros LB FF LK cr A M V a HH Ha HC [NC|[RO|BS]]; [| |exact (cwa_not_bshadow _ _ _ _ _ _ _ a HH HC BS)].
- apply NC. unfold aclient. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
+ left. exact HB.
+ right. left. rewrite (dla_sptop DL). pose proof Hsp. lia.
+ right. right. left. destruct (img_w_client lo hi Hin) as (lo' & hi' & Hin' & H1 & H2 & H3 & H4).
rewrite (dla_img_lo DL), (dla_img_hi DL). split; [lia|]. apply (dla_client DL lo' hi' a Hin'). lia.
- pose proof (dla_ro_img DL a RO) as RI. destruct HC as [HB|[HS|(lo & hi & Hin & Hr)]].
+ destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
+ pose proof Hsp. lia.
+ exact (dla_ro DL lo hi a Hin Hr RO).
Qed.
Lemma ainv_frame : forall LB FF LK cr A M M' (model model' : Model),
ri_inv HI LB FF LK cr A M (vml_of model) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
(forall a : word, M a <> None -> M' a <> None) ->
vml_of model' = vml_of model ->
ri_inv HI LB FF LK cr A M' (vml_of model').
Proof.
intros LB FF LK cr A M M' model model' HH FR GR EV. rewrite EV.
apply (aio_frame _ _ _ _ _ HIok LB FF LK cr A M M' _ HH); [|exact GR].
intros a Ha HP. apply FR; [exact Ha|]. intros HC. exact (cwa_not_private _ _ _ _ _ _ _ a HH Ha HC HP).
Qed.
Lemma sbm_vml : forall m m', same_but_materialized m m' -> vml_of m' = vml_of m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. split; reflexivity. Qed.
Lemma model_rt_fds : forall m m', model_rt m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' ->. destruct m; split; reflexivity. Qed.
Lemma sbm_rdrA : forall m m', same_but_materialized m m' -> m_channel_reader m' = m_channel_reader m.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma model_rt_rdr : forall m m', model_rt m m' -> m_channel_reader m' = m_channel_reader m.
Proof. intros m m' ->. destruct m; reflexivity. Qed.
Lemma regions_writeA : forall vals ebs bls LB FF LK cr A M V,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
ri_inv HI LB FF LK cr A M V ->
(forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A [] E (CWA LB) (fun _ => True).
Proof.
intros vals ebs bls LB FF LK cr A M V E P0 HH Hbl. pose proof Hsp as Hsp'.
constructor; cbn [ev E]; rewrite ?P0.
- lia.
- lia.
- intros z Hz Hnot. unfold CWA. right. left. lia.
- intros z Hz. right. exact I.
- intros i nb Hf. pose proof (sub_blockA_hz _ _ _ (Hbl i nb Hf)) as (Z1 & Z2 & Z3).
destruct (Hbl i nb Hf) as (cap & Hnb & Hin & HB). split; [lia|]. intros z Hz. unfold CWA. left.
exists (bv_unsigned (vals_ev vals i), cap). split; [exact Hin|]. cbn [fst snd]. lia.
- intros v b Hf. discriminate.
- intros i [].
- intros lo hi Hin. destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4).
split; [lia|]. split; [lia|]. intros a Ha. unfold CWA. right. right. exists lo, hi. auto.
- intros lo hi [].
Qed.
Lemma block_frame : forall vals ebs bls LB FF LK cr A M M' (model : Model) log,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
ri_inv HI LB FF LK cr A M (vml_of model) ->
(forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W_A log = true ->
mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
(forall a, ahid A model a = true -> M' a = M a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
/\ (forall a : word, M a <> None -> M' a <> None).
Proof.
intros vals ebs bls LB FF LK cr A M M' model log E P0 HH Hbl Hlog EQM EQH.
pose proof (regions_writeA vals ebs bls LB FF LK cr A M _ P0 HH Hbl) as RG.
split.
- intros a Ha HC. destruct (ahid A model (Z_to_bv 64 a)) eqn:Hh; [apply EQH; exact Hh|].
assert (E1 : M' (Z_to_bv 64 a) = mrestrict (ahid A model) M' (Z_to_bv 64 a)) by (unfold mrestrict; rewrite Hh; reflexivity).
rewrite E1, EQM.
rewrite (mem_denot_frame_Z ASEGS 0 (2 ^ 40) (2 ^ 40) bls [] [] IMG_W_A _ (CWA LB) (fun _ => True) [] RG _ log a Hlog Ha HC).
unfold mrestrict. rewrite Hh. reflexivity.
- intros a Hd. destruct (ahid A model a) eqn:Hh; [rewrite (EQH a Hh); exact Hd|].
assert (E1 : M' a = mrestrict (ahid A model) M' a) by (unfold mrestrict; rewrite Hh; reflexivity).
rewrite E1, EQM. apply (mem_denot_grows E (mrestrict (ahid A model) M) log a). unfold mrestrict. rewrite Hh. exact Hd.
Qed.
Variable M0 : word -> option byte.
Definition STKTOP : Z := Z.max (ar_sptop ar) (ar_stack_top ar).
Lemma stksh_rng : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V -> in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x ->
0x7fff8000 + 0xfffeff00000 <= x <= 0x7fff8000 + 0xfffffffffff /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x.
Proof.
intros LB FF LK cr A M V x HH HS. pose proof Hsp as Hsp'.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
unfold in_shadow_of, S, SB, STKTOP in *. rewrite (dla_sptop DL) in *.
assert (X2 : x <= 0x7fff8000 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8).
{ destruct HS as [_ HS]. replace (bv_unsigned sp0 - 8388608 + (Z.max (bv_unsigned sp0) (ar_stack_top ar) - (bv_unsigned sp0 - 8388608)) - 1)
with (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) in HS by ring. lia. }
assert (D1 : (0x7fff80000000 - 8388608) / 8 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_le_mono; lia).
assert (D2 : (Z.max (bv_unsigned sp0) (ar_stack_top ar) - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) by ring.
change ((0x7fff80000000 - 8388608) / 8) with 0xfffeff00000 in D1. change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2 |- *. lia.
Qed.
Record dinv (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop := DINV {
di_inv : ri_inv HI LB [] LK cr A M (vml_of model);
di_minv : MInv A model;
di_halt : m_halted model = None;
di_above : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a);
di_stksh : forall x, in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> byte_at M x 0;
di_hish : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> byte_at M x 0;
di_rdr : m_channel_reader model = true
}.
Lemma dinv_lzinv : forall LB LK cr A M model, dinv LB LK cr A M model -> lzinv ASEGS (ahid A model) A model.
Proof. intros LB LK cr A M model D. exact (lzinv_of_inv _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) (di_minv _ _ _ _ _ _ D) (di_halt _ _ _ _ _ _ D)). Qed.
Lemma stksh_not_cwa : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V ->
in_shadow_of (ahl_ceil ar) (STKTOP - ahl_ceil ar) x -> ~ CWA LB x.
Proof.
intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (stksh_rng _ _ _ _ _ _ _ x HH HS) as ((X1 & X2) & _).
destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
- destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
- lia.
- destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
Qed.
Lemma hish_rng : forall x, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> 0x7fff8000 + 0xfffeff00000 <= x <= 0x7fff8000 + 0xfffffffffff.
Proof.
intros x HS. pose proof Hsp as Hsp'. unfold in_shadow_of, S, SB, ahl_ceil in *. rewrite (dla_sptop DL) in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
clear - HS Hsp'. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma hish_not_cwa : forall LB FF LK cr A M V x, ri_inv HI LB FF LK cr A M V ->
in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> ~ CWA LB x.
Proof.
intros LB FF LK cr A M V x HH HS HC. pose proof Hsp as Hsp'. destruct (hish_rng x HS) as (X1 & X2).
destruct HC as [HB|[HSt|(lo & hi & Hin & Hr)]].
- destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF b Hb) as (HBR & _). destruct HBR as (_ & _ & _ & _ & _ & (_ & AM & _)). unfold BIGSHADOW_LO, BIGSHADOW_HI in AM. lia.
- lia.
- destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
Qed.
Lemma dinv_frame : forall LB LK cr A M M' (model model' : Model),
dinv LB LK cr A M model ->
(forall a, 0 <= a < 2 ^ 64 -> ~ CWA LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
(forall a : word, M a <> None -> M' a <> None) ->
vml_of model' = vml_of model -> MInv A model' -> m_halted model' = None ->
m_channel_reader model' = m_channel_reader model ->
dinv LB LK cr A M' model'.
Proof.
intros LB LK cr A M M' model model' D FR GR EV MI HL RD. pose proof Hsp as Hsp'. constructor.
- exact (ainv_frame _ _ _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D) FR GR EV).
- exact MI.
- exact HL.
- intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply FR; [lia|].
intros [HB|[HSt|(lo & hi & Hin & Hr)]].
+ destruct HB as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (WF & _).
destruct (WF b Hb) as (HBR & _). apply hzA_of_block_range in HBR. unfold hzA in HBR. lia.
+ lia.
+ destruct (img_w_client lo hi Hin) as (_ & _ & _ & _ & _ & H3 & H4). lia.
- intros x Hx. unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | | exact (stksh_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & _). lia.
- intros x Hx. unfold byte_at. rewrite FR; [exact (di_hish _ _ _ _ _ _ D x Hx) | | exact (hish_not_cwa _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx)].
pose proof (hish_rng x Hx). lia.
- rewrite RD. exact (di_rdr _ _ _ _ _ _ D).
Qed.
Lemma dinv_block : forall vals ebs bls LB LK cr A M M' (model model' : Model) log,
let E := Env (vals_ev vals) ebs in
vals_ev vals 0 = sp0 ->
dinv LB LK cr A M model ->
(forall i nb, find_nz i bls = Some nb -> sub_blockA LB (bv_unsigned (vals_ev vals i)) nb) ->
log_in_b 0 (2 ^ 40) (2 ^ 40) bls [] IMG_W_A log = true ->
mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
(forall a, ahid A model a = true -> M' a = M a) ->
lzinv ASEGS (ahid A model) A model' -> same_but_materialized model model' ->
dinv LB LK cr A M' model'.
Proof.
intros vals ebs bls LB LK cr A M M' model model' log E P0 D Hbl Hlog EQM EQH HZ SBM.
destruct (block_frame vals ebs bls LB [] LK cr A M M' model log P0 (di_inv _ _ _ _ _ _ D) Hbl Hlog EQM EQH) as (FR & GR).
destruct HZ as (_ & _ & _ & MI & HL).
exact (dinv_frame _ _ _ _ _ _ _ _ D FR GR (sbm_vml _ _ SBM) MI HL (sbm_rdrA _ _ SBM)).
Qed.
Lemma minv_same_vm : forall A (m m' : Model), m_vm m' = m_vm m -> MInv A m -> MInv A m'.
Proof.
intros A m m' EV [I1 I2 I3 I4 I5].
constructor; unfold m_vm_materialized, m_vm_lazy, m_vmmaps, eager_used, m_vmmaps, m_vm_lazy in *; rewrite EV; assumption.
Qed.
Lemma vml_same_vm : forall (m m' : Model), m_vm m' = m_vm m -> vml_of m' = vml_of m.
Proof. intros m m' EV. unfold vml_of, m_vmmaps, m_vm_lazy. rewrite EV. reflexivity. Qed.
Lemma with_fds_vm : forall f (m : Model), m_vm (with_fds f m) = m_vm m.
Proof. intros f m. destruct m. reflexivity. Qed.
Lemma with_fds_fs : forall f (m : Model), m_fs (with_fds f m) = m_fs m.
Proof. intros f m. destruct m. reflexivity. Qed.
Lemma with_fds_fds : forall f (m : Model), m_fds (with_fds f m) = f.
Proof. intros f m. destruct m as [[t p] v i fsy pr l tm]. reflexivity. Qed.
Lemma with_fds_rdr : forall f (m : Model), m_channel_reader (with_fds f m) = m_channel_reader m.
Proof. intros f m. destruct m. reflexivity. Qed.
Lemma ahid_same_lazy : forall A (m m' : Model), m_vm_lazy m' = m_vm_lazy m -> ahid A m' = ahid A m.
Proof. intros A m m' EL. unfold ahid. rewrite EL. reflexivity. Qed.
Lemma ahid_sbm : forall A (m m' : Model), same_but_materialized m m' -> ahid A m' = ahid A m.
Proof. intros A m m' SB. apply ahid_same_lazy. exact (sbm_lazy_eq _ _ SB). Qed.
Lemma dinv_model : forall LB LK cr A M (model model' : Model),
dinv LB LK cr A M model -> m_vm model' = m_vm model -> m_halted model' = None ->
m_channel_reader model' = m_channel_reader model -> dinv LB LK cr A M model'.
Proof.
intros LB LK cr A M model model' D EV HL RD.
apply (dinv_frame LB LK cr A M M model model' D); [reflexivity | auto | exact (vml_same_vm _ _ EV) | exact (minv_same_vm _ _ _ EV (di_minv _ _ _ _ _ _ D)) | exact HL | exact RD].
Qed.
Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
Lemma dinv_stack_defined : forall LB LK cr A M model, dinv LB LK cr A M model ->
defined M (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
Proof.
intros LB LK cr A M model D i Hi.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (di_inv _ _ _ _ _ _ D)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
rewrite (di_above _ _ _ _ _ _ D) by lia. apply M0_def. exact Hi.
Qed.
Lemma dinv_call : forall LB LBc LB' LK LK' cr cr' A A' M M' (model model' : Model) sp scr,
dinv LB LK cr A M model -> sp <= bv_unsigned sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBc [] sp scr a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
ri_inv HI LB' [] LK' cr' A' M' (vml_of model') -> MInv A' model' -> model_rt model model' ->
dinv LB' LK' cr' A' M' model'.
Proof.
intros LB LBc LB' LK LK' cr cr' A A' M M' model model' sp scr D Hsp1 PR HH' MI RT. pose proof Hsp as Hsp'. constructor.
- exact HH'.
- exact MI.
- rewrite (model_rt_halted _ _ RT). exact (di_halt _ _ _ _ _ _ D).
- intros a Ha. rewrite <- (di_above _ _ _ _ _ _ D a Ha). apply PR; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
- intros x Hx. destruct (stksh_rng _ _ _ _ _ _ _ x (di_inv _ _ _ _ _ _ D) Hx) as (X & XC).
unfold byte_at. rewrite PR; [exact (di_stksh _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact XC].
- intros x Hx. pose proof (hish_rng x Hx) as X.
unfold byte_at. rewrite PR; [exact (di_hish _ _ _ _ _ _ D x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx].
- rewrite (model_rt_rdr _ _ RT). exact (di_rdr _ _ _ _ _ _ D).
Qed.
Lemma amalloc_site : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "[M'<'V8yR0%211%411'=y8%611%811p041'T6%;11'T7%=11&R0y5%221='?%11;p0@1'QG'A'Q5%2211%H11&S4%J11&RB%72G6%M11'QI%O11!p]021'T5(T2&T?rA%211r@%5221&T<r1r>%33251&T:&T@r2&R:&RMr9r=%3221%521:%94871?'J'8&T>&;rD%22QI1rB%5221(B%93821&T=rE%92R01%3217%>3=16'Q1u1rF%?2R61%4231rG(5%Q9221vV3%H3R<21&S@%11?%K3J1C&SI(V6+2(G%33R821%52F1&V7&TD&V9%12RJ>%321Q:%52RL1%Q83RL71'I&TE&TI&TJ+F%22@1%411%621QLz%82QN1%:231&TGr?+@%3221%QH3RI17rH+:%N3S31L%Q0231%K2SBR?%QN3SB21&TF%12?QJ+K%F2Q41%I2QM1%K241&RKvQ=rC%332QM1rK+4%Q>3SC1Q<%Q@231+V^Rf0%Q<2T31%R?3T331rL+1%QE3SJ1QC%QG231%RD3T81G%Q;2Q4R?+R0%Q;2QI1%I2RB1%Q@241%Q62CQL%RK3SL1Q:'S?rJrIrNrM%56AH4321%T81T3&R=%12S<6(6%12T7SC%S73531&Q2r3rQ7%S82TO1%4231&SBrQ0%T2256%R<2U51%4331SI%R9261p0<1p[FTE1pZNU71rQ8%SD2U;1%@2?1%T<23@%RF2U?1%RA21T3%RC241p0F1pZ2TO1p\HUA1(>%11TJ%SA11&7rQ<&SOr5%211%53UL41%TL1TF%TN216%T82UOTC&NrQ>%T;2V21uQ0%4221%TA3V361rQ?%T@2V71u:%9221%U92Q=1r4%SF2V=1%TI3V=31&T0&Q3%VB1V4&T8&SF%443VA21rQ@%TN2VE1%83E31%UA3QJ1U8r7r8%U<221%U>21U<&SHrQA%U72VN1%O21GrQ6%5221&SGrQ5+TP0rQ4rQ3%554321Q6%QA3VO71%UO4UNN>1(9(@%14VIVIDR>rQ;%43VJ21rQ:&RLrQ9%23SH1RDr:%S46652K1V5&S6rQ=%2214&TB%13W5:6&RIvTO%24T219=&RAr;%231BQI&S8r<%23TI1R:%U52U:VL+Q?%U52UC1%TC2VO1%U:241%UB2X9VL%V?11rQE%113%VH3WM31p061pYNWK1%UA2U:W8%TM2W9T5%UD221&RDrQD%221W8%UO2XFSH%VN11rQG%113%W53X:31p061p0:1pYNX91&TA%QC4X;X;T1WB&SC%33X<21%V32RFWE%U?2WFT5%V6221%VL1?rQJ%11A%WC3XH31p051p091pYNXG1pZJXH1p[6XI1'SMvUN(QE&SJvU;%VL2YCSJ&SL%11X9%554WM3UJ1%721WL%:4X<91R:p0<1p0M1p0Q<1p0QI1p0QM1p0R11p0R51p0R81p0R<1p0RH1p0S;1p0SF1p0SO1tR@Y6T71t\LZ5T:1p\FYD1p4YC1p[BYH1pT6YJ1pT@YN1+_T\@%WG2Z>1%N5MS91S8JrQ2%Q1221%Q44Y6Q31W4p071p0TM1p0U11p0U<1p0V11p0V81p0V;1p0VA1p0VG1p0VO1p0W41p0W;1p0WB1p0WH1p0X41p0XB1p0XF1p0XL1p0Y21p0Y81p0YC1p0YN1tR>Z9Z31pRJZ;1p[LZG1p\NZA1pZ4ZB1p\4ZJ1p[DZK1p2ZJ1pZ>ZH1pS4ZJ1pRNZM1p[@[21pT4[41pT>[81p[4[<1p\:[?1pZD[B1p\J[H1").
Proof.
intros vals ebs sr kn R M model LB LK cr A n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R10 Hn Hcr R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
pose proof (aio_malloc _ _ _ _ _ HIok fx R M model LB FF LK cr A n K) as MS.
cbv zeta in MS. rewrite (dla_segs DL), (dla_malloc DL), (dla_tp DL) in MS. rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia.
eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
- unfold amalloc_post. intros R' M' model' A' u HA HP HBR HAP HFA HDEF HSHB HPRES HRT HINC HMI' HH'.
rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (HA' : vals_ev (vals ++ junk_vals R') (length vals + 10) = Z_to_bv 64 u) by (rewrite vals_ev_junkA by lia; exact HA).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_malloc L) a)
by (intros a; apply aclient_scr_mono; lia).
apply (CONT R' M' model' A' u HL' HA'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
+ apply Forall_app. split.
* eapply kn_blkA_ok; [exact HA' | exact P0' | exact HBR |].
intros i Hi. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH'); [apply HDEF; exact Hi | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; lia |].
right. right. exists (u, n). split; [left; reflexivity | cbn [fst snd]; lia].
* unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
-- eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB ((u, n) :: LB) FF FF LK LK cr (adebit L cr n) A A' M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
++ intros a Ha; exact Ha.
++ intros a (b & Hb & Hr). exists b. split; [right; exact Hb | exact Hr].
++ intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
++ intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
-- intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
-- intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_malloc L)) as [Hlo|Hhi].
++ rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
++ apply PR2. lia.
+
apply (dinv_call LB LB ((u, n) :: LB) LK LK cr (adebit L cr n) A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_malloc L) DI ltac:(lia)); assumption.
+ intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
+ intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
+ intros lo hi a Hin Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
split; [destruct (img_client_rng lo hi Hin) as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin Ha)].
Qed.
Lemma in_lb_remove_in : forall u (LB : list (Z * Z)) b, In b (lb_remove u LB) -> In b LB.
Proof.
intros u LB b. induction LB as [|c LB' IH]; [intros []|]. cbn [lb_remove].
destruct (Z.eqb (fst c) u); [intros H; right; exact H|]. intros [<-|H]; [left; reflexivity | right; apply IH; exact H].
Qed.
Lemma in_block_remove : forall u LB a, in_block (lb_remove u LB) a -> in_block LB a.
Proof. intros u LB a (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr]. Qed.
Lemma afree_site : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "ZJ'<'V8yR0%211%411'=y8%611%811p041'T6%;11'T7%=11&R0y5%221='?%11;p0@1'QG'A'Q5%2211%H11&S4%J11&RB%72G6%M11'QI%O11!p]021'T5(T2&T?rB%211rA%5221&T<r1r?%33251&T:&T@r2&R:&RMr:r>%3221%521:%94871?'J'8&T>&;rE%22QI1rC%5221(B%93821&T=rF%92R01%3217%>3=16'Q1u1rG%?2R61%4231rH(5%Q9221vV3%H3R<21&S@%11?%K3J1C&SI(V6+2(G%33R821%52F1&V7&TD&V9%12RJ>r=%4221%62RM1%Q93RM81'I&TE&TI&TJ+F%22A1%411%621QEz%82QG1%:231&TG+@%22R31%QH3RI16&TA(@%14RLRLR=R;%33RL1QArJ+:%Q23S71Q0%Q4231%O2SFQK%R23SF21rK+4%Q83S=1Q6%Q:231+V^Rf0%Q62SM1%R93SM31rL+1%Q?3SD1Q=%QA231r@%Q=2T41%R@3T431%Q62OS1&TF+R0%Q72QF1%32S51%Q<251%Q22S9QI%RH3SI1Q6'S?rIrNrM%46CJQ0321%T41SO&R=%12S8R<(6%12T3S?%S33531&Q2r3rQ7%S42TK1%4231&SB&RErQ0%22Q21%T0278%R:2U31%6331SG%R6281p0>1p[FTC1pZNU51rQ8%SB2U91%B2A1%T:23B%RD2U=1%R>21T1%R@241p0H1pZ2TM1p\HU?1(>%11TH%SL11&7rQ;&SOr4%211%53UJ41%TJ1TD%TL216%T62UMTA&NrQ=%T92V01uQ0%4221%T?3V161&T0rQ<&Q3%V91UK&T8&SF%443V821rQ>%TE2V<1%93831r7%U93U321r5r6%U4221%U6215&SGrQ2+TP0rQ1%45321QIC%U?4U>R061rQ5rQ9%QN221r8%RA62QFR4=1@&S6%12Q:3&TB%13V>QJ5%T42T:UL+Q?%T42TC1%S02UO1%T9241%TB2W9UL%T?11rQ@%113%UH3VM31p061pYNVK1%T@2T9V8%S:2V9S8%TC221&RDrQ?%RF2QN1%321V9%U02WGRM%V?11rQB%113%V63W;31p061p0;1pYNW:1%T@4W;W;S5VB&SC%TC3W<21%U22R9VE%SL2VFS9%U5221%W21>rQE%11@%VC3WH31p051p091pYNWG1pZJWH1p[6WI1'SMvUN(QE&SJvU;rQ6%UM2XD1&SL%11W:%655W>3W61%821UM%;4W=:1QNp0=1p0M1p0Q=1p0QJ1p0QM1p0R01p0R61p0RA1p0RN1tR@X3S61t\LY2S91p4X?1p[BXD1pT6XF1pT@XJ1rQ4+_T\<%VD2Y;1rQ3%L5K421G%N21RH%Q14X3Q01W9p081p0SL1p0T01p0T;1p0U21p0U81p0U;1p0UB1p0UJ1p0V21p0V91p0V>1p0VC1p0VO1p0W>1p0WB1p0WH1p0WN1p0X41p0X?1p0XJ1tR>Y5XO1pRJY71p[LYC1p\NY=1pZ4Y>1p\4YF1p[DYG1p\FYH1p2YG1pZ>YE1pS4YG1pRNYJ1p[@YO1pT4Z11pT>Z51p[4Z91p\:Z<1pZDZ?1p\JZE1").
Proof.
intros vals ebs sr kn R M model LB LK cr A u n so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal Hin R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
pose proof (aio_free _ _ _ _ _ HIok fx R M model LB FF LK cr A u n K) as MS.
cbv zeta in MS. rewrite (dla_segs DL), (dla_free DL), (dla_tp DL) in MS. rewrite R1 in MS.
apply MS; clear MS; try assumption.
- apply ret_ok_even. rewrite u_small by lia. exact Hra2.
- rewrite R2, u_small by lia.
eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia.
- intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (CLI : forall a, aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 a ->
aclient L ar (lb_remove u LB) FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
by (intros a; apply aclient_scr_mono; lia).
apply (CONT R' M' model' A' HL'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
+ unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa (lb_remove u LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
* eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove u LB) LB (lb_remove u LB) FF FF LK LK cr cr A A' M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
-- intros a Ha. exact (in_block_remove u LB a Ha).
-- intros a Ha; exact Ha.
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
* intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
* intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
-- rewrite PR1; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
-- apply PR2. lia.
+
apply (dinv_call LB (lb_remove u LB) (lb_remove u LB) LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
+ intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop DL). lia.
+ intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
+ intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
Qed.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Section SE.
Variables (Mx : word -> option byte).
Lemma rdn_of_bytes_at : forall n (a : word) bs, length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall j, (j < n)%nat -> Mx (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
rdn ASEGS Mx a n = Some bs.
Proof.
intros n.
induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
- destruct bs; [reflexivity | cbn in Hlen; lia].
- destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen. cbn [rdn].
pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
rewrite H0.
destruct n as [|n']; [destruct bs'; [reflexivity | cbn in Hlen; lia]|].
assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv bs'); [reflexivity | lia | rewrite Hu1; lia |].
intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (Datatypes.S j)) by lia.
exact (Hpt (Datatypes.S j) ltac:(lia)).
Qed.
End SE.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aacc_of_blkA : forall M u n p m, shadow_blk M u n -> u mod 8 = 0 -> 0 <= u -> u <= p -> p + m <= u + n -> aacc M p m.
Proof.
intros M u n p m.
intros [SZ SP] U8 U0 H1 H2 a Ha.
unfold shadow_zero, byte_at in SZ, SP |- *.
assert (E : S a = S u + (a / 8 - u / 8)) by (unfold S; lia).
destruct (Z_lt_le_dec (a / 8 - u / 8) (n / 8)) as [LT|GE].
- left. rewrite E. apply SZ. lia.
- right. exists (n mod 8). assert (NZ : n mod 8 <> 0) by lia. assert (G : a / 8 - u / 8 = n / 8) by lia.
split; [rewrite E, G; apply SP; exact NZ | lia].
Qed.
Lemma u16_u8 : forall u, u mod 16 = 0 -> u mod 8 = 0.
Proof. intros u H. lia. Qed.
Lemma S_mono : forall a b, a <= b -> S a <= S b.
Proof. intros a b H. unfold S. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma src_blk_aacc : forall LB FF LK cr A M V (As caps src n : Z),
ri_inv HI LB FF LK cr A M V -> In (As, caps) LB -> As <= src -> src + n <= As + caps -> aacc M src n.
Proof.
intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (As, caps) Hin) as (HBR & _ & HSB & _). cbn [fst snd] in HBR, HSB. destruct HBR as (B1 & _ & B3 & _).
apply (aacc_of_blkA M As caps src n HSB (u16_u8 _ B3)); lia.
Qed.
Lemma src_blk_app_rng : forall LB FF LK cr A M V (As caps src n : Z),
ri_inv HI LB FF LK cr A M V -> In (As, caps) LB -> As <= src -> src + n <= As + caps -> app_rng ar src n.
Proof.
intros LB FF LK cr A M V As caps src n HH Hin H1 H2.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (As, caps) Hin) as (HBR & _). cbn [fst snd] in HBR. destruct HBR as (B1 & _ & _ & _ & B5 & (_ & BAM & _)).
unfold app_rng. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
Lemma src_stage_app_rng : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "B'Q5&TE+V[lT@r2%3221&TDr3%2214+V]lT@%8221&RNvTOr4%33217p051p0;1p[D@1p\<A1").
Proof. intros src n H1 H2. pose proof Hsp. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. rewrite (dla_sptop DL). lia. Qed.
Lemma src_stage_aacc : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "Q@'<'A'Q5%2211%411&S4%611&RB'V8yR0%211'?y8%511%311p051&S9&S7vQ;r9r8r7r6r5r4r3%9887654321&TE+V[lT@%2214&TD%1276+V]lT@%6221&RH%13><;p031p081p0<1p[DQ51p\<Q61pYLI1pT4K1p2Q71pZ>Q51pS4Q71pRBQ81pRNQ;1").
Proof.
intros LB FF LK cr A M V src n HH H1 H2 a Ha. left.
destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH src n) as (Z0 & _).
- rewrite (dla_img_lo DL). lia.
- rewrite (dla_img_hi DL). lia.
- lia.
- rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- apply Z0. unfold in_shadow_of. split; apply S_mono; lia.
Qed.
Lemma aclient_remove : forall u LB FF sp scr a, aclient L ar (lb_remove u LB) FF sp scr a -> aclient L ar LB FF sp scr a.
Proof.
intros u LB FF sp scr a Hc. unfold aclient, aclient_g in *.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; [left; exact (in_block_remove u LB a Hc) | tauto | tauto | tauto | tauto | tauto |].
right. right. right. right. right. right. destruct Hc as (b & Hb & Hr). exists b. split; [exact (in_lb_remove_in u LB b Hb) | exact Hr].
Qed.
Lemma ablock_range_prefix : forall u n nb, ablock_range L ar u n -> 0 < nb <= n -> ablock_range L ar u nb.
Proof. intros u n nb (B1 & B2 & B3 & B4 & B5 & (B6 & B7 & B8)) Hnb. unfold ablock_range, app_mem. repeat split; lia. Qed.
Lemma kn_blkA_of_inv : forall vals ebs LB LK cr A M (model : Model) v (u cap nb : Z),
let E := Env (vals_ev vals) ebs in
dinv LB LK cr A M model -> In (u, cap) LB -> 0 < nb <= cap ->
vals_ev vals v = Z_to_bv 64 u -> vals_ev vals 0 = sp0 ->
know_ok ASEGS E (mrestrict (ahid A model) M) (kn_blkA v nb).
Proof.
intros vals ebs LB LK cr A M model v u cap nb E D Hin Hnb Pv P0.
pose proof (di_inv _ _ _ _ _ _ D) as HH.
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (u, cap) Hin) as (HBR & HDEF & _). cbn [fst snd] in HBR, HDEF.
eapply kn_blkA_ok; [exact Pv | exact P0 | exact (ablock_range_prefix _ _ _ HBR Hnb) |].
intros i Hi. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ (u + i) HH); [apply HDEF; lia | destruct HBR as (B1 & _ & _ & _ & B5 & _); rewrite (dla_sptop DL) in B5; pose proof Hsp; lia |].
right. right. exists (u, cap). split; [exact Hin | cbn [fst snd]; lia].
Qed.
Lemma amemcpy_site : ltac2:(TCodec.tc2 tcn__Jb0DrvLib "]4'<'V8yR0%211%411'=y8%611%811p041'T6%;11'T7%=11&R0y5%221='?%11;p0@1'QG'A'Q5%2211%H11&S4%J11&RB%72G6%M11'QI%O11!p]021'T5(T2&T?rF%211rE%5221&T<r1rC%33251&T:&T@r2&R:&RMr>rB%3221%521:%94871?'J'8&T>&;rI%22QI1rG%5221(B%93821&T=rJ%92R01%3217%>3=16'Q1u1rK%?2R61%4231rL(5%Q9221vV3%H3R<21&S@%11?%K3J1C&SI(V6+2(G%33R821%52F1&V7&TD&V9%12RJ>r=%4221%62RM1%Q93RM81'I&TE&TI&TJ+F%22A1%411%621QFz%82QH1%:231&TGr?+@%3221%QI3RJ17rM+:%O3S41M%Q1231rD%M2SD1%R03SD31rN+;%Q63S;1Q4%Q8231%R53SI16rO+<%Q;3S@1Q9%Q=231%R:3SN1;&TF%12JRL+K%Q12Q@1%Q42RO1%Q6241rQ1+4%QF3SK1QD%QH231+V^Rf0%QD2T;1%RG3T;31rQ2+1%QM3T21QK%QO231%QJ2TAS0%RM3TA21%QC2Q<S:+R0%QC2R21%F2S=1%QH241%Q>2Q5R5%S43T51QB'S?rQ0rQ4rQ3%46AH3Q321&TA(@%14T=T=Q6Q;%33T=15%R328Q=%R<2Q9QE%R=2O:%R6221&RHrQ8%231Q>QC%R:2R3?+Q?%R:2RI1%R=281&RNvTO%231Q3Q:%RA2R:T9%QB2T:E%RD221'M+RPP0rQ5%RO21T:%RH231+Vb\P0%QJ231%RL231&RDrQ<%2217%;241p0=1pZNU=1%UC1UL&SKrQ=%S>2V5Q9&TL%11Q:%54TL431(6%12V4QM%TF3931rQ6%SE21QA%S>21H%SG2IQC%S@214%M231%V31UN&R=%12U7QH%<2V1U=%U13421&Q2r3rQG%U22VI1%4231&SB&RErQ@%22Q21%UN278%T82W11%6331UE%T4281p0>1p[FVA1pZNW31rQH%U@2W71%B2A1%V823B%TB2W;1%T<21UO%T>241p0H1pZ2VK1p\HW=1(>%11VF%S=11&7rQJ&SO%11O%43WG31%VG1VA%VI215%V32WJV>&NrQL%V62WM1uQ0%4221%V<3WN61&T0rQK&Q3%X61WH&T8&SF%443X521rQM%VB2X91%93831r6%W63W021rQDr5%W1221%W3215&SG+TP0rQ;%35RA2RH1B%W;4W:QN51rQFrQEr7%T06QCR1321>&S6%12Q73r9%V72XN@rQB%RJ11%RN4WE431rQA%RJ2XM1%W?3S231%U52WMT@%V72SE1%S;2NWJ&L%V92R2RA%VB2R3C%U;2RC1%V=231%511r4%VH2Y?1%X011rR1%113%WN3Y331p071p0>1p0@1pYNY31%TH4Y4Y4S0X;&SC%TK3Y521%VK2=X>%UL2X?S4%VN221r@%W82YOS7%211rR3%113%X>3YC31p071p0;1pYNYB1pZJYC1p[6YD1'SMvUN(QE&SJvU;%WG2Z>S@r<&SL%11Y5%655WG431r;%9221rQ?%=4Y:<21p0?1p0Q11p0QE1p0QN1p0R11p0R61p0R@1p0RM1tR@YOS51t\LZNS81p[BZ?1pT6ZA1pT@ZE1+^m`8%X>2[51rQC%K5JRI21F%M21R9%Q04YMO1V<p071p0SH1p0SL1p0T71p0TM1p0U41p0U?1p0V11p0V51p0V91p0V;1p0V?1p0VC1p0VE1p0VJ1p0W01p0W31p0W91p0W@1p0WH1p0WO1p0X51p0X;1p0XC1p0XI1p0Y51p0YD1p0YH1p0YN1p0Z41p0Z:1p0ZE1p0[01tR>[;[51pRJ[=1p[L[I1p\N[C1pZ4[D1p\4[L1pZ6\;1p[D[N1p\<[O1pZB\01pZ:\11p6\21p2\11pZ>[O1pS4\11pRN\41p[@\91pT4\;1pT>\?1p[4\C1p\:\F1pZD\I1p\J\O1").
Proof.
intros vals ebs sr kn R M model LB LK cr A Ad capd dst src n bs so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
R2 Hso Hsoal R10 R11 R12 Hn R4 R1 Hra Hra2 DI Hin Hd1 Hd2 Hacc Hs0 Hs1 Happ Hsrc Hrd Hdj Hbl Hvb HK0 CONT.
set (FF := @nil fframe) in *.
pose proof (di_inv _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ DI) as HMI.
pose proof (dinv_stack_defined _ _ _ _ _ _ DI) as Hdef.
pose proof Hsp as Hsp'. pose proof (dla_scr DL) as (SC1 & SC2 & SC3).
destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _).
destruct (WF (Ad, capd) Hin) as (HBR & HDEF & HSB & _ & HAP & _). cbn [fst snd] in HBR, HDEF, HSB, HAP.
pose proof (hzA_of_block_range _ _ HBR) as (Y1 & Y2 & Y3). pose proof HBR as (_ & _ & B3 & _ & _ & (_ & BAM & _)).
assert (INB : forall i, 0 <= i < n -> in_block LB (dst + i)).
{ intros i Hi. exists (Ad, capd). split; [exact Hin | cbn [fst snd]; lia]. }
pose proof (aic_memcpy_libc _ _ _ _ _ ICok fx R M model LB FF LK cr A dst src n bs K) as MS.
unfold amemcpy_libc_spec, amemcpy_spec_at in MS. rewrite (dla_segs DL), (dla_memcpy DL) in MS.
apply MS; clear MS; try assumption.
- unfold amem_pre. rewrite (dla_tp DL), (dla_segs DL), R1, R2, u_small by lia.
split; [exact HH|]. split; [exact Hh|]. split; [exact HMI|]. split; [exact R10|]. split; [exact R12|]. split; [lia|].
split; [exact R4|]. split; [apply ret_ok_even; rewrite u_small by lia; exact Hra2|].
split; [eapply (astack_ok_of_window vals ebs (ahid A model) M kn so); eauto; lia|].
split; [apply (aacc_of_blkA M Ad capd dst n HSB (u16_u8 _ B3)); lia|].
split; [intros i Hi; left; exact (INB i Hi)|].
split; [|split; [exact HK0 | unfold app_rng; rewrite (dla_sptop DL); lia]].
intros i m Hi Hm. destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
apply store_ok_of_all; [rewrite u_small by lia; lia|].
intros x Hx. rewrite u_small in Hx by lia.
specialize (HDEF (bv_unsigned x - Ad) ltac:(lia)). replace (Ad + (bv_unsigned x - Ad)) with (bv_unsigned x) in HDEF by lia.
rewrite Z_to_bv_bv_unsigned in HDEF. unfold wview. destruct (M x); [discriminate | exfalso; apply HDEF; reflexivity].
- split; assumption.
- intros i Hi. destruct (Hsrc i Hi) as [X|X]; [left; rewrite (dla_img_lo DL), (dla_img_hi DL); exact X | right; left; exact X].
- intros _. exact Hdj.
- unfold amem_post. cbv zeta. intros R' M' model' HA HP HNEW HPRES HSCR HRT HMI' HH'.
rewrite (dla_segs DL), R1. rewrite R2, u_small in HPRES, HSCR by lia.
assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
assert (NDST : forall a, aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> ~ (dst <= a < dst + n)).
{ intros a Hc Hr. unfold aclient, aclient_g in Hc. rewrite (dla_img_lo DL), (dla_img_hi DL), (dla_sptop DL) in Hc.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & Hbr). destruct (HAP b Hb) as [Q|Q]; lia.
- lia.
- lia.
- destruct Hc as (f & [] & _).
- unfold in_shadow_of, S, SB in Hc. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
assert (D0 : 0 <= (bv_unsigned sp0 - 8388608) / 8) by (apply Z.div_pos; lia).
replace (bv_unsigned sp0 - 8388608 + (2 ^ 47 - (bv_unsigned sp0 - 8388608)) - 1) with (2 ^ 47 - 1) in Hc by ring.
change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in Hc. lia.
- destruct Hc as (f & [] & _).
- destruct Hc as (b & Hb & Hbr). pose proof (in_lb_remove_in _ _ _ Hb) as Hb'.
destruct (WF b Hb') as ((C1 & _ & _ & C4 & C5 & (_ & _ & C8)) & _).
unfold in_shadow_of, S, SB in Hbr. unfold BIGSHADOW_LO, BIGSHADOW_HI in BAM.
assert (D0 : 0 <= fst b / 8) by (apply Z.div_pos; lia).
assert (D2 : (fst b + snd b - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
change ((2 ^ 47 - 1) / 8) with 0xfffffffffff in D2. lia. }
assert (PR1 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hc. apply HPRES; [exact Ha | | exact (NDST a Hc)].
apply (aclient_scr_mono _ _ _ 4096 (hl_scr_mem L)); [lia|]. exact (aclient_remove Ad LB FF _ _ a Hc). }
apply (CONT R' M' model' HL'); try assumption.
+ apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA R R' HP) c_kept_no0A).
+ unfold keep_allocA.
pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
(Env (vals_ev (vals ++ junk_vals R')) ebs)
(CPa (lb_remove Ad LB) FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A model')) (SCa (bv_unsigned sp0 + so) 4096)
_ (mrestrict (ahid A model) M) (mrestrict (ahid A model') M') _ _ kn HK1).
* eapply (regions_callA (vals ++ junk_vals R') ebs so 4096 bls vbnd (lb_remove Ad LB) LB LB FF FF LK LK cr cr A A M M' model model');
[exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
-- intros a Ha. exact (in_block_remove Ad LB a Ha).
-- intros a Ha. exact (in_block_remove Ad LB a Ha).
-- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
-- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
* intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; assumption.
* intros a HS. unfold SCa in HS. unfold mrestrict.
rewrite (vis_of_inv _ _ _ _ _ _ _ a HH') by lia.
destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_mem L)) as [Hlo|Hhi].
-- rewrite HPRES; [apply (window_defined vals ebs (ahid A model) M kn HK Hiw P0); lia | lia | | lia].
unfold aclient. right. left. rewrite (dla_sptop DL). lia.
-- apply HSCR. lia.
+
apply (dinv_call LB (lb_remove Ad LB) LB LK LK cr cr A A M M' model model' (bv_unsigned sp0 + so) 4096 DI ltac:(lia)); assumption.
+
pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
apply rdn_of_bytes_at; [exact Hlen | rewrite u_small by lia; lia |].
intros j Hj. rewrite u_small by lia.
destruct (HNEW (Z.of_nat j) ltac:(lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id in Hnth.
unfold byte_at in Hb. rewrite Hb. f_equal. symmetry. apply nth_error_nth. exact Hnth.
+ intros a Ha Hb Hnd. apply HPRES; [exact Ha | left; exact Hb | exact Hnd].
+ intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
{ destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo DL), (dla_img_hi DL).
split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client DL lo hi a Hin' Ha)].
Qed.
End DrvLayoutA.
End FPX_1.
