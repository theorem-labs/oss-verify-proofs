(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0DefsK Ja0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
Ja0HandoffK Ja0ArtCellsK Ja0BssZeroK AsanNodesLibEK AsanNodesMmLibK HandoffLazyK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA As0Tables ArtMem ArtRunsMem JatLeaf JatPoison JatRzLog JatAllocA JatCls JatDepotA JatDepot
ArtRuns ArtBridge JatInitCache JatInv JatFsInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0ArtHandoffK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffCellsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffLedgerK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffRolesK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ArtCellsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ArtHandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0ArtHandoffK.Derive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0BssZeroK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BUDGET"; "1None"; "1O"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"]; ["1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "3lt"; "4Z"; "0E"; "0FULL"; "0L"; "0Li"]; ["5segments_reserved"; "6m_vm_lazy"; "6m_vmmaps"; "6page_base"; "6page_in_ranges"; "6vm_maps"; "6vm_noaccess"; "0Lj"; "7BINV"; "7KN0"; "7in_shadow_rw"; "8apart"; "8cell"; "8wr"; "9aev"; ":class_size"]; [";A_wf"; ";page_allowedb"; "<HSub"; "<a_ghost"; "<a_hlz"; "<a_maps"; "<a_vis"; "<amap"; "<e_sp0"; "<eaddz"; "<hop"; "<kn"; "<no_fog"; "=pagedown"; "=pageup"; "=uE"]; [">ELit"; ">ealign"; ">env"; ">expr"; "?chk_word"; "?chk_wr"; "?chk_zero"; "@hops_in_maps"; "Arbase"; "Arlen"; "Bbyte_at"; "Bfframe"; "Bshadow_allowed"; "Bshadow_blk"; "Bvml_of"; "CART_LITW"]; ["EK0D"; "Eas0_A0x"; "Eas0_BASEx"; "Eas0_EXTRA"; "DE_RISX"; "DI_BLK"; "DI_KSPACE"; "DI_PARR"; "Dall_true"; "Dapx"; "Dart_sym_list"; "Das0_rn"; "DbBLK"; "DbK"; "Dglob_chk"; "Dhop_pre"]; ["Dhop_zone"; "Dhsplit"; "Dimg_cover"; "Dis_rng"; "Dis_var_in"; "Dlit_len"; "Down_ok"; "DspbE"; "Dvis_hi"; "Dvis_in"; "Dxlo_pos"; "FDEP_HI"; "FDEP_LO"; "GASEGS0"; "Hart_c_statics"; "Hart_fsg"]; ["Hart_fsg0"; "Hart_fsinv"; "Hart_fsinv_handoff"; "Iart_client_ok"; "Iart_eager_ok"; "Iart_handoff_target"; "Iart_kn_ok"; "Iart_rt_statics"; "Iart_rt_thread"; "Iart_run_ok"; "Irn_HI"; "Jloaded_segments"; "Keqb"; "LIn"; "Lexistsb"; "Lforallb"]; ["Madd"; "Mdiv"; "Meqb"; "Mle"; "Mlt"; "Mmodulo"; "Mmul"; "Mof_nat"; "Mpow"; "Msub"; "0a"; "0b"; "0b0"; "0c"; "0cs"; "0e"]; ["0g"; "0h"; "0h1"; "0h2"; "0hi"; "0i"; "0j"; "0l"; "0lo"; "0m"; "0model"; "0n"; "0off"; "0p"; "0q"; "0r"]; ["NZ_to_bv"; "Nbv"; "Nbv_unsigned"; "0sz"; "0v"; "0w"; "0x"; "0z"; "0zb"; "0zh"; "0zl"; "0zn"]]).
Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
Definition I_KSPACE : nat := 5. Definition I_PARR : nat := 6. Definition I_THREAD : nat := 7. Definition I_CTX : nat := 8.
Definition I_FAKE : nat := 11. Definition I_L2 : nat := 14. Definition I_BLK : nat := 15. Definition I_DTLS : nat := 10.
Definition e_at (k : list kentry) (b : expr) (off : Z) (w : nat) : expr :=
match kfind_word k b off w with Some e => e | None => ELit 0 end.
Definition bT (cs : acs) : expr := am_base (role cs I_THREAD).
Definition bC (cs : acs) : expr := am_base (role cs I_CTX).
Definition bF (cs : acs) : expr := am_base (role cs I_FAKE).
Definition bP (cs : acs) : expr := am_base (role cs I_PARR).
Definition bL2 (cs : acs) : expr := am_base (role cs I_L2).
Definition bBLK (cs : acs) : expr := am_base (role cs I_BLK).
Definition bD (cs : acs) : expr := am_base (role cs I_DTLS).
Definition spbE (cs : acs) : expr := e_at (kn cs) (ELit 0) (1275544 + 32) 8.
Definition bK (cs : acs) : expr := fst (split_lit (spbE cs)).
Definition topE (cs : acs) : expr := e_at (kn cs) (bT cs) 8 8.
Definition botE (cs : acs) : expr := e_at (kn cs) (bT cs) 16 8.
Definition tfE (cs : acs) : expr := e_at (kn cs) (ELit 0) 0x20cbc8 8.
Definition stE (cs : acs) : expr := e_at (kn cs) (ELit 0) (0x20cbc8 + 24) 4.
Definition TP : Z := 0x66ed80.
Definition TSD : Z := 0x690238.
Definition LOFF : Z := 0x10.
Definition as0_ar (E : env) (cs : acs) : asan_run :=
AR (uE E e_sp0) (uE E (topE cs)) (uE E (botE cs)) (rbase E cs I_FAKE) (uE E (bK cs) + 0x10000).
Definition as0_rn (E : env) (cs : acs) : art_run :=
ARN (as0_ar E cs) (rbase E cs I_THREAD) (rbase E cs I_CTX) TP 0 TSD LOFF ((uE E (bK cs) + 0x10000) / 65536)
(rbase E cs I_KSPACE) (rbase E cs I_PARR) (rbase E cs I_L2) (rbase E cs I_BLK) (rbase E cs I_DTLS).
Definition is_var_in (k : list kentry) (e : expr) (lo hi : Z) : bool :=
match e with EVar _ => existsb (kentry_eqb (KRange e lo hi)) k | _ => false end.
Definition B1 : Z := 3497168.
Definition B2 : Z := 5998180.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
existsb (fun K => match K with KImg l h => (Z.leb l lo && Z.leb hi h)%bool | _ => false end) k.
Definition xlo_pos (k : list kentry) (e : expr) : bool := match xlo k e with Some lo => Z.ltb 0 lo | None => false end.
Definition lit_len (cs : acs) (i : nat) (L : Z) : bool := expr_eqb (am_len (role cs i)) (ELit L).
Definition vis_in (cs : acs) (b n : expr) : bool := existsb (fun p => (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool) (a_vis cs).
Definition glob_chk (k : list kentry) (g : Z * Z) : bool :=
(chk_zero k (ELit 0) (fst g / 8 + 0x7fff8000) (snd g / 8) && (if Z.eqb (snd g mod 8) 0 then true else chk_word k (ELit 0) (fst g / 8 + 0x7fff8000 + snd g / 8) 1 (ELit (snd g mod 8)))
&& (0x10000 <=? fst g) && (fst g <? 0x691000) && (0 <=? snd g) && (snd g <? 4096))%bool.
Definition art_sym_list (cs : acs) : list bool :=
let k := kn cs in
[ ((17 =? Z.of_nat (length (a_maps cs))));
(chk_word k (ELit 0) (1275544 + 32) 8 (spbE cs));
(Z.eqb (snd (split_lit (spbE cs))) 0x10000);
(chk_word k (ELit 0) (1275544 + 48) 8 (eaddz (spbE cs) (2 ^ 37)));
(chk_word k (ELit 0) (1275544 + 64 + 8) 8 (bP cs));
(chk_word k (ELit 0) TSD 8 (bC cs));
(chk_word k (bC cs) 152 8 (bT cs));
(chk_word k (bT cs) 0 8 (bC cs));
(chk_word k (bC cs) 8 4 (ELit 0));
(chk_word k (bT cs) 8 8 (topE cs));
(chk_word k (bT cs) 16 8 (botE cs));
(chk_word k (bT cs) 40 1 (ELit 0));
(chk_word k (bT cs) 3168 1 (ELit 0));
(chk_wr k (bT cs) 0 4096);
(chk_zero k (bT cs) 80 3088);
(chk_zero k (bK cs) 0x2000010000 4096);
(chk_wr k (bK cs) 0x2000010000 4096);
(chk_wr k (bF cs) 0 0xb09000);
(chk_word k (ELit 0) TP 8 (bF cs));
(chk_word k (bT cs) 72 8 (bF cs));
(chk_word k (bF cs) 88 8 (ELit 20));
(chk_zero k (bF cs) 0 88);
(chk_zero k (bF cs) 96 (4096 + 32768 - 96));
(chk_word k (ELit 0) 0x61cbe8 8 (bL2 cs));
(chk_word k (ELit 0) (0x20cbc8 + 16) 8 (bBLK cs));
(chk_word k (ELit 0) 0x20cbc8 8 (tfE cs));
(is_var_in k (tfE cs) 2 3);
(chk_word k (ELit 0) (0x20cbc8 + 24) 4 (stE cs));
(is_var_in k (stE cs) 2 3);
(chk_wr k (ELit 0) 0x21cbd8 4194308);
(chk_wr k (ELit 0) 0x20cbc8 32);
(chk_wr k (bL2 cs) 0 (2 ^ 20));
(chk_wr k (bBLK cs) 0 (2 ^ 23));
(chk_word k (bL2 cs) 24 4 (ELit 0));
(chk_word k (bL2 cs) 16 8 (e_at k (bL2 cs) 16 8));
(chk_word k (ELit 0) B1 4 (e_at k (ELit 0) B1 4));
(is_var_in k (e_at k (ELit 0) B1 4) 0 1);
(chk_word k (ELit 0) B2 4 (e_at k (ELit 0) B2 4));
(is_var_in k (e_at k (ELit 0) B2 4) 0 1);
(img_cover k DEP_LO B1);
(img_cover k (B1 + 4) B2);
(img_cover k (B2 + 4) DEP_HI);
(amap_eqb (role cs 0) M_LOW);
(amap_eqb (role cs 1) M_GAP);
(amap_eqb (role cs 2) M_HIGH);
(xlo_pos k (bT cs));
(xlo_pos k (bC cs));
(xlo_pos k (bF cs));
(lit_len cs I_KSPACE 0x2000011000);
(lit_len cs I_PARR 0x800000);
(lit_len cs I_THREAD 4096);
(lit_len cs I_CTX 0x10000);
(lit_len cs I_FAKE 0xb09000);
(lit_len cs I_L2 0x100000);
(lit_len cs I_BLK 0x800000);
(lit_len cs I_DTLS 4096); (xlo_pos k (bD cs)); (chk_word k (ELit 0) (1275544 + 64 + 16) 8 (bP cs)); (vis_in cs (ELit 0x10000) (ELit 0x681000));
(vis_in cs (bF cs) (ELit 0xb09000));
(vis_in cs e_top e_stk_len);
(img_cover k 0x12c000 0x134000);
(chk_word k (ELit 0) (TP + 8) 8 (bD cs)); (chk_word k (bD cs) 24 8 (ELit TP));
(chk_zero k (ELit 0) 2147459072 9760); (chk_zero k (ELit 0) 2147468836 8); (chk_zero k (ELit 0) 2147468860 44); (chk_zero k (ELit 0) 2147469084 135832); (chk_zero k (ELit 0) 2147604936 5216); (chk_zero k (ELit 0) 2147610312 701240);
(forallb (glob_chk k) ART_GLOBALS) ]%bool.
Definition art_sym_chk (cs : acs) : bool := forallb (fun b => b) (art_sym_list cs).
Fixpoint all_true (l : list bool) : Prop := match l with [] => True | b :: r => b = true /\ all_true r end.
Lemma all_true_of : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "?'<'7%211'E&SOr1qXH51%33612(C%63821&RHr2%211p041pY@<1").
Proof. induction l as [|b l IH]; intros H; [exact I|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. split; [exact H1 | exact (IH H2)]. Qed.
Definition bKS (cs : acs) : expr := am_base (role cs I_KSPACE).
Definition E_RISX (cs : acs) : expr := EAlu Instr.ALU_ADD (bK cs) (ELit 0x2000010000).
Fixpoint hsplit (r : expr) (h : list hop) : option (list hop * list hop) :=
match h with
| [] => None
| HSub b n :: t =>
if (expr_eqb b r && expr_eqb n (ELit 4096))%bool then Some ([], t)
else match hsplit r t with Some (h1, h2) => Some (HSub b n :: h1, h2) | None => None end
| x :: t => match hsplit r t with Some (h1, h2) => Some (x :: h1, h2) | None => None end
end.
Lemma hsplit_eq : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q4'R3'<'QJ%211'E'?'A%1244%311&S1r4r3%3221(4(@r2r1%34>>21%52;1%?3;71&6(8(QBr5(R0+TP0%211%5241%73J1=%93KB1%J3KD1p0<1pY8M1pY6N1pY4O1pZ0Q31").
Proof.
intros r h. induction h as [|x t IH]; intros h1 h2 H; [discriminate|]. cbn [hsplit] in H.
destruct x as [b n|b n].
- destruct (hsplit r t) as [[a1 a2]|] eqn:Hs; [|discriminate]. injection H as <- <-. cbn [app]. f_equal. apply IH. reflexivity.
- destruct (expr_eqb b r && expr_eqb n (ELit 4096))%bool eqn:Hb.
+ injection H as <- <-. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply expr_eqb_eq in B2. subst. reflexivity.
+ destruct (hsplit r t) as [[a1 a2]|] eqn:Hs; [|discriminate]. injection H as <- <-. cbn [app]. f_equal. apply IH. reflexivity.
Qed.
Definition is_rng (b n : expr) (b0 : expr) (L : Z) : bool := (expr_eqb b b0 && expr_eqb n (ELit L))%bool.
Definition hop_pre (cs : acs) (x : hop) : bool :=
match x with HSub _ _ => true | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000)%bool end.
Definition hop_zone (cs : acs) (x : hop) : bool :=
match x with
| HSub _ _ => true
| HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000 || is_rng b n (bKS cs) 0x2000011000
|| is_rng b n (ELit 0x7fff7000) 0x10000000 || is_rng b n (ELit 0x8fff7000) 0x20000000000 || is_rng b n (ELit 0x2008fff7000) 0xdfff0001000)%bool
end.
Definition vis_hi (k : list kentry) (p : expr * expr) : bool :=
((expr_eqb (fst p) e_top && expr_eqb (snd p) e_stk_len)
|| match xhi k (fst p), snd p with Some hi, ELit n => (0 <=? n) && (n <? 2 ^ 64) && (hi + n <=? 2 ^ 47) | _, _ => false end)%bool.
Definition apx (k : list kentry) (zb : expr) (zn : Z) (p : expr * expr) : bool :=
let '(zb', zk) := split_lit zb in let '(pb, pk) := split_lit (fst p) in
(flat_x k zb' zk (ELit zn) && flat_x k pb pk (snd p) && ranges_apart_x k zb' zk (ELit zn) pb pk (snd p))%bool.
Definition own_ok (cs : acs) (p : expr * expr) : bool :=
let k := kn cs in
(is_rng (fst p) (snd p) (bBLK cs) 0x800000
|| is_rng (fst p) (snd p) (E_RISX cs) 4096
|| (apx k (bKS cs) 0x2000011000 p && apx k (bP cs) 0x800000 p
&& (apx k (bBLK cs) 0x800000 p || (expr_eqb (snd p) (ELit 4096) && (12 <=? ealign k (fst p))))))%bool.
Definition art_lazy_chk (cs : acs) : bool :=
(match hsplit (E_RISX cs) (a_hlz cs) with Some (h1, _) => forallb (hop_pre cs) h1 | None => false end
&& forallb (hop_zone cs) (a_hlz cs)
&& forallb (fun p => vis_hi (kn cs) p && own_ok cs p) (a_vis cs ++ a_ghost cs)
&& (12 <=? ealign (kn cs) (bBLK cs)) && vis_in cs (bBLK cs) (ELit 0x800000))%bool.
Lemma uE_lit : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "I'R2'K'D&T3zr1%3221&T4&T8+2+R0%3221%5271%;271'E&QOr3(R0r2%211%5241%73D13p091pZ@F1pQJH1").
Proof. intros E z Hz. unfold uE. cbn [edenot]. apply u64_lit. exact Hz. Qed.
Lemma class_size_pos : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "A'K'D&T3+1r1%3221+N%5231%7231&T4z&Q?r2%211%5241p071pXL@1").
Proof.
intros c Hc. assert (H : forallb (fun c => 0 <? AsanTab.class_size c) (AsanTab.zrange 1 30) = true) by (vm_compute; reflexivity).
apply Z.ltb_lt. apply (proj1 (forallb_forall _ _) H). unfold AsanTab.zrange. apply AsanTab.in_ziota. change (Z.of_nat (Z.to_nat 30)) with 30. lia.
Qed.
Section Derive.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.
Variable cs : acs.
Hypothesis CHK0 : as0_chk cs = true.
Hypothesis CHKL : art_lits_chk cs = true.
Hypothesis CHKS : art_sym_chk cs = true.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
#[local] Notation rn := (as0_rn E cs).
#[local] Notation T := (rbase E cs I_THREAD).
#[local] Notation CTX := (rbase E cs I_CTX).
#[local] Notation KB := (rbase E cs I_KSPACE).
#[local] Notation SPB := (uE E (bK cs) + 0x10000).
#[local] Notation SP0 := (uE E e_sp0).
Hypothesis HGEO_SPB : KB < SPB <= KB + 65536 /\ SPB mod 65536 = 0.
Hypothesis HGEO_STK : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
/\ SP0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= SP0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.
Hypothesis HSP16 : SP0 + 16 <= 2 ^ 47.
Hypothesis HSPA : SP0 mod 16 = 0.
Ltac chk_split H := repeat (let X := fresh "C" in apply andb_prop in H as [H X]).
#[using="CHK0"] Lemma nofog : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "9'E'7&QL&QEvT>%211%411(C%83721").
Proof. pose proof CHK0 as H. unfold as0_chk in H. chk_split H. exact H. Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH R model HC"] Lemma cellW : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q0'R3'K'='E'7&R4&QKvT>%211r4r3r2r1%8554321(C%<3;21&Q<&SKvM&T0&QOvLr5%3221%521?%524>%:5982@1p0<1pZ:L1pZ<K1pYJM1pXHO1").
Proof.
intros b off w v H. unfold cell.
exact (proj2 (hc_word ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off w v HC H)).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma cellL : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "G'K'=&SM'A%1243%2215(@r3r2%349821r1%547;21&R?%;3821&Q<&SKvMr4%45321;:p061pZ:D1pZ<D1pXFF1").
Proof. exact (art_lit sp brk0 rdraw argv envp uid hw fs Hsp Hva E cs R FULL model HC CHKL). Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma cellLb : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q7'K'='E'7&SN'A%1265%2217&5&T2&:r1%236<1%33=<1r4%6221&SL&B%13BA6r3%4221%=261%53@F;r2%?221%A241qXLC1&R?%H3E21(C%L3K21&Q<&SKvM%3521D?;p051pZ:Q41pZ<Q41pXFQ61").
Proof.
intros a w v H. apply existsb_exists in H as ([[a' w'] v'] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
exact (cellL _ _ _ Hin).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs R model HC"] Lemma cellZ : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QB'R3'K'='E'7&R6&QKvT>%211r5r4r3%744321(C%;3:21'Ir2u8%3221&T3&T0&QOvLr7%3221r6%6221%821A&T7%11C%:2E1r8%;2:1%=21:%>219%@251&Q<&SKvMz%4532?O1p061p0?1p0I1p0N1pZ<Q;1pXFQ=1pYHQ>1pYJQ?1pXHQA1").
Proof.
intros b off n a w H Hw H1 H2. unfold cell.
exact (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H a w Hw H1 H2).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH R model HC"] Lemma wrK : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "L'R3'K'E'7&R5&QKvT>%211r3r2r1%744321(C%;3:21&Q=&SKvM&T0&QOvLr4%3221%521>%94871>p0;1pYHH1pYJI1pXHK1").
Proof.
intros b off n H d k Hd Hk.
exact (hc_wr ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off n HC H d k Hd Hk).
Qed.
#[using="CHKS E"] Lemma len17 : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK ":'E'=&;'QG&QEvT>%211%5241uA%93821").
Proof. pose proof (all_true_of _ CHKS) as H. cbn [all_true art_sym_list] in H. destruct H as [H _]. apply Z.eqb_eq in H. lia. Qed.
#[using="CHKS"] Lemma sym_all : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "5&RH&RJvT>%211%411").
Proof. exact (all_true_of _ CHKS). Qed.
Ltac chk_old := let H := fresh in pose proof sym_all as H; cbn [all_true art_sym_list] in H; decompose [and] H; assumption.
Ltac chk_find eqt g l i :=
lazymatch l with
| cons ?hd ?tl =>
first [ (eqt hd g;
exact (proj1 (List.Forall_nth (fun xb : bool => (fun yb : bool => yb) xb = true) (art_sym_list cs))
(proj2 (List.Forall_forall (fun xb : bool => (fun yb : bool => yb) xb = true) (art_sym_list cs))
(proj1 (List.forallb_forall (fun yb : bool => yb) (art_sym_list cs)) CHKS))
i true (proj1 (Nat.ltb_lt i (length (art_sym_list cs))) (@eq_refl bool true))))
| chk_find eqt g tl constr:(Datatypes.S i) ]
end.
Ltac chk :=
first [ lazymatch goal with
| |- ?g = true =>
let l := eval cbv beta zeta delta [art_sym_list] in (art_sym_list cs) in
first [ chk_find ltac:(fun u v => constr_eq u v) g l constr:(Datatypes.O) | chk_find ltac:(fun u v => unify u v) g l constr:(Datatypes.O) ]
end
| chk_old ].
#[using="sp brk0 rdraw argv envp uid hw fs cs R FULL model HC HSP16"] Lemma sp0_win : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK ">'D&T3+SoonPPPPP0&QOvL&QH%3221%6251&T8+2+Q?%3221%;261%=261").
Proof. destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & W & _). unfold sp_window_lo, sp_window_hi in W. unfold uE in *. lia. Qed.
#[using="CHKS"] Lemma role_shadow : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q1'D'E'K&R8vLvT>(3%43321+QoonlP0%83721&R9%13765+XPPPP0%<3;21u1%<3;:1+RWonlP0%@3?21%83>=4+RPPPPPPP0%C3B21u2%C3BA1+RPRWonlP0%G3F21%?3ED4+]oohPPTP0%J3I21%L241%M291%N2=1%O2B1%Q02G1").
Proof.
assert (H0 : amap_eqb (role cs 0) M_LOW = true) by chk. assert (H1 : amap_eqb (role cs 1) M_GAP = true) by chk.
assert (H2 : amap_eqb (role cs 2) M_HIGH = true) by chk.
apply amap_eqb_eq in H0. apply amap_eqb_eq in H1. apply amap_eqb_eq in H2. unfold rbase, rlen. rewrite H0, H1, H2.
cbn [M_LOW M_GAP M_HIGH am_base am_len]. rewrite !uE_lit by lia. repeat split; reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_rg := (ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "R9'='K&Jr2uA%3221'E'7&S5vT>r3%33218(C%73621'D&T3z%2217&T4&T8+2+R0%3221%52=1%:271&T5&R8vLr5%332D1+TP0%6221%J3O1@%B2A4r4%A2C1&T0%1283&T9&QO&QH%22>1+XPPP0%5221%M271'H+RPP0%Q02:1+VbTP0%Q221D%5231'Iu3%221Ir6%M3LQ>1%D21L+QoonlP0%Q;221+`PQoooPP0%Q=215%@231p091%QA2=1%QB2D1%QC2N1%QD2Q11%QE2Q31p0Q<1p0QH1p0R11pQNR61pY<R81")) (only parsing).
Variable i : ltac:(sec_ty2 constr:(SEC_T_rg) 0%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_rg) 1%nat 0%nat).
Lemma rg : ltac:(sec_stmt2 constr:(SEC_T_rg) 2%nat 0%nat).
Proof using sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK i L.
intros Hi HL HLr.
unfold lit_len in HL. apply expr_eqb_eq in HL.
pose proof (role_lit E cs i L HL HLr) as El.
destruct (role_geo ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i HC nofog ltac:(rewrite len17; exact Hi)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
rewrite El in *. cbn [img_lo img_hi ASAN0] in G4.
repeat split; try assumption. intros H3.
destruct role_shadow as (S0 & L0 & S1 & L1 & S2 & L2).
pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 0 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A0.
pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 1 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A1.
pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 2 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A2.
rewrite El, ?S0, ?L0, ?S1, ?L1, ?S2, ?L2 in *. lia.
Qed.
End SE.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC"] Lemma ra : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QH'='K&Jr4uA%3221&G'Er6r5%33:21%511'7&S5vT>r7%33217(C%;3621'D&T3z%2217&T4&T8+2+R0%3221%52=1%:271'H&T0&R8vLr;%332E1r9%6221r:%736I1%D231r8%;231%G218%>241p0@1p0A1p0M1p0N1p0Q61p0Q=1p0Q>1pR@QC1pR0QD1pY>QF1pY<QG1").
Proof.
intros i j Li Lj Hi Hj Hne HLi HLj Ri Rj. unfold lit_len in *. apply expr_eqb_eq in HLi. apply expr_eqb_eq in HLj.
pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i j HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; exact Hj) Hne) as D.
rewrite (role_lit E cs i Li HLi Ri), (role_lit E cs j Lj HLj Rj) in D. exact D.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC"] Lemma xpos : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "D'R3'E'7&S:&QKvT>%211r1%5221(C%93821&T4z&QOvLr2%3221%6251p081pY0C1").
Proof.
intros e H. unfold xlo_pos in H. destruct (xlo (kn cs) e) as [lo|] eqn:Hx; [|discriminate]. apply Z.ltb_lt in H.
pose proof (xlo_sound ASEGS0 E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx). unfold uE. lia.
Qed.
Ltac lenok := first [assert_succeeds (idtac); (chk)].
Ltac RG i L := let X := fresh "G" in pose proof (rg i L ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(lia)) as X.
Ltac RA i j Li Lj := let X := fresh "D" in
pose proof (ra i j Li Lj ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia)
ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as X.
#[using="HGEO_SPB"] Lemma spb_qs : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "@'E'K&T6+RPP0&T1&T0&QOvL&RMvT>%211%5241%7219%921:%<2;1%?3>13").
Proof. destruct HGEO_SPB as (_ & Hm). pose proof (Z.div_mod SPB 65536 ltac:(lia)). lia. Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rgl : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QE'='K&Jr2uA%3221'E'7&S5vT>r3%33218(C%73621'D&T3z%2217&T4&T8+2+R0%3221%52=1%:271&T5&R8vLr5%332D1+TP0%6221%J3O1@%B2A4r4%A2C1&T0%1283&T9&QO&QH%22>1+XPPP0%5221%M271%O2:1%Q02=1%Q12?1p0H1p0Q41p0Q=1pQNQB1pY<QD1").
Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (G1 & G2 & G3 & G4 & _). auto. Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg_img : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q;'='K&Jr2uA%3221'E'7&S5vT>r3%33218(C%73621'D&T3z%2217&T4&T8+2+R0%3221%52=1%:271'H&T0&R8vLr5%332E1r4%6221+RPP0%C221+VbTP0%E216%<231p0>1p0J1p0Q31pQNQ81pY<Q:1").
Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (_ & _ & _ & _ & G5 & _). exact G5. Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg_hole : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q?'='K'D'Iu3r2%3221&JuA%2241%8241'E'7&S5vT>r3%3321;(C%73621&T3z%2216&T4&T8+2+R0%3221%52<1%J271'H&T0&R8vLr5%332D1r4%6221+QoonlP0%C221+`PQoooPP0%E216%<231p0>1p0I1p0Q21pQNQ<1pY<Q>1").
Proof. intros i L Hi HL HLr. destruct (rg i L ltac:(lia) HL HLr) as (_ & _ & _ & _ & _ & G6). apply G6. lia. Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC"] Lemma ra_sub : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "R6'='K&Jr8uA%3221&G'Er:r9%33:21%511'7&S5vT>r;%33217(C%;3621'D&T3z%2217&T4&T8+2+R0%3221%52=1%:271&R8vLr?%332C1%>21C&T0r<%221Fr@%938I1r>%6221%F251%G24LrA%?3>O1%;21>%K2:1&Q;r=%24B:1>p041p091p0;1p0D1p0J1p0K1p0Q71p0Q81p0Q@1p0QG1p0QH1pYDQM1pXHQN1pYHQO1pXFR01pR@R11pR0R21pY>R41pY<R51").
Proof.
intros i j Li Lj a n b m Hi Hj Hne HLi HLj Ri Rj Ha Hn Hb Hm. unfold apart.
destruct (ra i j Li Lj Hi Hj Hne HLi HLj Ri Rj) as [X|X]; [left | right]; lia.
Qed.
Ltac IDX := unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK, I_DTLS; lia.
Ltac RASUB i j Li Lj := apply (ra_sub i j Li Lj); [IDX | IDX | IDX | chk | chk | lia | lia | lia | lia | lia | lia].
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_run_ok : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "6&SI&RKvLvT>%3221%511").
Proof.
pose proof sp0_win as W. pose proof spb_qs as Q. destruct HGEO_SPB as ((K1 & K2) & K3).
pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
pose proof (rgl I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (t1 & t2 & t3 & t4).
pose proof (rgl I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (c1 & c2 & c3 & c4).
pose proof (rgl I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (l1 & l2 & l3 & l4).
pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
pose proof (rgl I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (f1 & f2 & f3 & f4).
pose proof (xpos (bT cs) ltac:(chk)) as PT. pose proof (xpos (bC cs) ltac:(chk)) as PC. pose proof (xpos (bF cs) ltac:(chk)) as PF.
change (uE E (bT cs)) with T in PT. change (uE E (bC cs)) with CTX in PC. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
assert (QT : exists qt, T = 4096 * qt) by (exists (T / 4096); pose proof (Z.div_mod T 4096 ltac:(lia)); lia).
assert (T4 : 4096 <= T) by (destruct QT as [qt Eq]; lia).
assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
assert (KHOLE : 0x10007fff8000 <= KB).
{ destruct (rg_hole I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia. }
unfold art_run_ok, art_geo, rn_HI, rn_spb, rn_ris, rn_spb, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES.
cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_tp rn_key rn_tsd rn_loff rn_qs rn_kbase rn_parr rn_l2 rn_blk ar_sptop ar_space_beg ar_fs]. unfold TP, TSD, LOFF.
rewrite Q. change (2 ^ 20) with 0x100000. change (2 ^ 23) with 0x800000.
split.
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact T4|]. split; [lia|]. split; [exact (rg_img I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [exact (rg_hole I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [exact QT|].
split; [exact C4|]. split; [lia|].
split; [destruct (rg_img I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [destruct (rg_hole I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
split; [RASUB I_THREAD I_CTX 4096 0x10000|]. lia. }
split; [reflexivity|]. split; [exact g1|]. split; [lia|]. split; [lia|].
split; [exact p1|].
split; [destruct (rg_img I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|]. split; [lia|].
split; [split; [lia|]; split; [|lia]; exact (rg_hole I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [RASUB I_L2 I_THREAD 0x100000 4096|]. split; [RASUB I_L2 I_CTX 0x100000 0x10000|]. split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|].
split; [unfold apart; destruct (rg_hole I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [RASUB I_BLK I_THREAD 0x800000 4096|]. split; [RASUB I_BLK I_CTX 0x800000 0x10000|]. split; [RASUB I_BLK I_KSPACE 0x800000 0x2000011000|].
split; [unfold apart; destruct (rg_hole I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
split; [RASUB I_PARR I_THREAD 0x800000 4096|]. split; [RASUB I_PARR I_CTX 0x800000 0x10000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
split; [RASUB I_PARR I_L2 0x800000 0x100000|]. split; [RASUB I_PARR I_BLK 0x800000 0x800000|].
split; [RASUB I_FAKE I_THREAD 0xb09000 4096|]. split; [RASUB I_FAKE I_CTX 0xb09000 0x10000|]. split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
split; [RASUB I_FAKE I_L2 0xb09000 0x100000|]. split; [RASUB I_FAKE I_BLK 0xb09000 0x800000|]. split; [RASUB I_FAKE I_PARR 0xb09000 0x800000|].
split; [lia|].
split; [split; [lia|]; split; [|lia]; exact (rg_hole I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [exact (rg_img I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|]. split; [exact F4|].
pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
cbn [as0_rn rn_dtls].
split; [destruct (rg_img I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
split; [destruct (rg_img I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
split; [exact D4|]. split; [lia|].
split; [exact (rg_img I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [split; [lia|]; split; [|lia]; exact (rg_hole I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
split; [RASUB I_DTLS I_THREAD 4096 4096|]. split; [RASUB I_DTLS I_CTX 4096 0x10000|]. split; [RASUB I_DTLS I_KSPACE 4096 0x2000011000|].
split; [RASUB I_DTLS I_PARR 4096 0x800000|]. split; [RASUB I_DTLS I_L2 4096 0x100000|]. split; [RASUB I_DTLS I_BLK 4096 0x800000|].
split; [RASUB I_DTLS I_FAKE 4096 0xb09000|].
split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
exact KHOLE.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Lemma spb_val : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "?'E'K&QOvL&S7vT>%211%5241&T0&RM%115%9281+RPP0%5221%>3=71").
Proof.
assert (Hs : Z.eqb (snd (split_lit (spbE cs))) 0x10000 = true) by chk. apply Z.eqb_eq in Hs.
pose proof (split_lit_denot E (spbE cs) (bK cs) 0x10000) as Hd. unfold bK in Hd |- *.
pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold bK in K1, K2.
destruct (split_lit (spbE cs)) as [b k] eqn:Hspl. cbn [fst snd] in *. subst k. specialize (Hd eq_refl).
unfold uE in *. rewrite Hd. apply u64_lit. lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Lemma ris_val : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "F'E'K&QOvL&QI&S7vT>%211&T8+2+Q5%3221%8251%;2:1&T0&RM%11:%?2>1+RPP0%5221%6219%E3D81").
Proof.
unfold eaddz, uE. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u64_lit by lia. fold (uE E (spbE cs)). rewrite spb_val.
apply Z.mod_small. pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold uE in *. lia.
Qed.
#[using="cs"] Lemma uE0 : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "9'E'K&QOvL(R0z%211%5241%83713").
Proof. apply uE_lit. lia. Qed.
Ltac CL := apply cellLb; vm_compute; reflexivity.
Ltac CW a w v := let X := fresh in pose proof (cellW (ELit 0) a w v ltac:(chk)) as X; rewrite uE0 in X; rewrite ?Z.add_0_l in X.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH cs CHKS E R model HC"] Lemma got_none : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "K'K'D&T3+QU`P0r1%3221&T4+QV`P0%2241%8241'E'?'U1y8%211%411vM&U0yR0r2%3221%511(2%119%>3931p0@1pXFJ1").
Proof.
intros a Ha. assert (H : img_cover (kn cs) 0x12c000 0x134000 = true) by chk.
unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
apply (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_rt_statics : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "7&SG&RKvLvT>%3221vM%6221").
Proof.
unfold art_rt_statics, art_rt_tlsgot, art_prim_consts, art_layout, art_tsd, art_alloc_rodata, art_rz_rodata, DRoD, rn_spb, rn_ris, rn_spb, SB, kHighMemEnd.
cbn [as0_rn rn_qs rn_tp rn_key rn_tsd rn_ctx rn_t rn_loff]. unfold TP, TSD, LOFF. rewrite spb_qs.
pose proof (cellW (ELit 0) (1275544 + 32) 8 (spbE cs) ltac:(chk)) as X1. rewrite uE0, spb_val in X1.
pose proof (cellW (ELit 0) (1275544 + 48) 8 (eaddz (spbE cs) (2 ^ 37)) ltac:(chk)) as X2. rewrite uE0, ris_val in X2.
pose proof (cellW (ELit 0) TSD 8 (bC cs) ltac:(chk)) as X3. rewrite uE0 in X3. unfold TSD in X3.
pose proof (cellW (bC cs) 152 8 (bT cs) ltac:(chk)) as X4.
change (uE E (bC cs)) with CTX in *. change (uE E (bT cs)) with T in *.
RG I_THREAD 4096. RG I_CTX 0x10000. pose proof sp0_win.
pose proof (xpos (bC cs) ltac:(chk)) as PC. change (uE E (bC cs)) with CTX in PC.
assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
repeat match goal with |- _ /\ _ => split end; try exact X1; try exact X2; try exact X3; try exact X4; try exact got_none; try CL; lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHKL CHKS R model HC"] Theorem as0_art_rt_thread : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "7&SH&RKvLvT>%3221vM%6221").
Proof.
unfold art_rt_thread. cbn [as0_rn as0_ar rn_t rn_ctx rn_tp rn_loff rn_ar ar_stack_top ar_stack_bottom]. unfold TP, LOFF.
pose proof (wrK (bT cs) 0 4096 ltac:(chk)) as W. rewrite Z.add_0_r in W.
pose proof (cellW (bT cs) 0 8 (bC cs) ltac:(chk)) as X1. rewrite Z.add_0_r in X1.
pose proof (cellW (bC cs) 8 4 (ELit 0) ltac:(chk)) as X2. rewrite uE0 in X2.
pose proof (cellW (bT cs) 8 8 (topE cs) ltac:(chk)) as X3. pose proof (cellW (bT cs) 16 8 (botE cs) ltac:(chk)) as X4.
pose proof (cellW (bT cs) 40 1 (ELit 0) ltac:(chk)) as X5. rewrite uE0 in X5.
pose proof (cellW (bT cs) 3168 1 (ELit 0) ltac:(chk)) as X6. rewrite uE0 in X6.
repeat match goal with |- _ /\ _ => split end; try assumption. CL.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Lemma kshadow_wr : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "H&Q=&SKvM&T0+QoooPP0&T6+XP0&T1&QOvL&RMvT>%211%5241+RPP0%<221%9212%<2;1%?2>1&T8+2+Q2%3221%G4FE51").
Proof.
destruct (as0_chk_parts cs CHK0) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3). RG I_KSPACE 0x2000011000.
destruct G as (g1 & g2 & g3 & g4 & g5 & g6). specialize (g6 ltac:(unfold I_KSPACE; lia)).
pose proof (Z.div_mod SPB 65536 ltac:(lia)) as DM. rewrite K3 in DM.
set (q := SPB / 65536) in *.
apply art_wr_of_defined; [lia | lia |].
intros x Hx.
apply (hl_shadow_defined ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH asan0_shadow_ok ltac:(cbn; unfold SHB_LO; lia)
E cs R FULL model HC C1 C4 C5 M_HIGH 0x2008fff7000 0xdfff0001000 C8 eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
Qed.
#[using="cs E"] Lemma wr0 : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "8'K&Q=&SKvMr1z%544321pXF71").
Proof. intros a d k Hd Hk. assert (k = 0%nat) by lia. subst k. reflexivity. Qed.
Section SE.
Variables (FSG : Type).
Variables (gfs0 : FSG).
Variables (k0 : nat).
Theorem as0_art_rt_primary : art_rt_primary FSG rn (art_gs0 FSG gfs0 k0) FULL.
Proof using sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKS R model HC HGEO_SPB HGEO_STK HSP16 FSG gfs0 k0.
unfold art_rt_primary. cbn [art_gs0 g_inited g_cls as0_rn rn_t rn_qs]. unfold rn_spb, rn_ris, rn_spb. cbn [as0_rn rn_qs]. rewrite spb_qs.
assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
assert (ZR : chk_zero (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
assert (WR : chk_wr (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
split; [|split; [|exact kshadow_wr]].
- intros c Hc. split; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
- intros c Hc. split; [|split; [|split; [|split]]].
+ unfold art_cls_rep, art_cache_rep, art_region_rep, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length]. change (Z.of_nat 0) with 0.
pose proof (wrK (bK cs) 0x2000010000 4096 WR) as W.
repeat match goal with |- _ /\ _ => split end;
try (apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia);
try (apply (cellZ (bK cs) 0x2000010000 4096 _ _ ZR); lia);
try (intros j Hj; cbn in Hj; lia); try apply wr0.
apply (wr_sub _ _ _ _ _ _ W); lia.
+ unfold art_cls_ok, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length app]. pose proof (class_size_pos c Hc).
repeat match goal with |- _ /\ _ => split end; try lia; try (exists 0; lia); try constructor.
+ unfold art_cls0. cbn [cl_cache]. intros H. congruence.
+ exists 0. reflexivity.
+ unfold art_cls0. cbn [cl_au]. intros H. lia.
Qed.
End SE.
#[using="Type"] Theorem as0_art_rt_chunks : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_chunks FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
Proof.
intros FSG gfs0 k0. unfold art_rt_chunks. cbn [art_gs0 g_cls g_st]. unfold art_cls0. cbn [cl_cache cl_free cl_au cl_mu app].
intros c Hc. pose proof (class_size_pos c Hc) as Hs. split; [|split; [|split]].
- intros x Hx. lia.
- intros w [].
- intros w _. reflexivity.
- intros w (W1 & W2 & _). lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma lock_sec : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "<&Q<&SKvM&T0+QVmdH+R0%3221+c8%5221u4z%;5:9321").
Proof.
apply (cell0_cat FULL (1275544 + 64 + 616) 1 3); [lia | lia | lia | CL | CL].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma lock_quar : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK ":&Q<&SKvM&T0+QVn[@+TH%3221u4z%9587321").
Proof.
apply (cell0_cat FULL (0x137970 + 152) 1 3); [lia | lia | lia | CL |].
apply (cell0_cat FULL (0x137970 + 152 + 1) 1 2); [lia | lia | lia | CL | CL].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHKL CHKS R model HC"] Theorem as0_art_rt_sec : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_sec FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
Proof.
intros FSG gfs0 k0. unfold art_rt_sec. cbn [art_gs0 g_sec g_sec_committed g_log as0_rn rn_parr length]. change (Z.of_nat 0) with 0.
pose proof (cellW (ELit 0) (1275544 + 64 + 8) 8 (bP cs) ltac:(chk)) as X. rewrite uE0 in X.
pose proof (cellW (ELit 0) (1275544 + 64 + 16) 8 (bP cs) ltac:(chk)) as X2. rewrite uE0 in X2.
repeat match goal with |- _ /\ _ => split end; try exact lock_sec; try CL; try exact X; try exact X2.
- intros H. congruence.
- intros H. discriminate H.
- intros i s H. destruct i; discriminate H.
- intros p [].
- lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHKL CHKS R model HC"] Theorem as0_art_rt_quar : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_quar FSG rn (art_gs0 FSG gfs0 k0) FULL.
Proof.
intros FSG gfs0 k0. unfold art_rt_quar. cbn [art_gs0 g_qt g_qg as0_rn rn_t length app map art_batches_bytes fold_right]. change (Z.of_nat 0) with 0.
assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
repeat match goal with |- _ /\ _ => split end; try lia; try exact lock_quar; try CL.
- exists 0, 0. repeat split; try reflexivity; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
- exists 0, 0. repeat split; try reflexivity; CL.
- constructor.
- intros b [].
- intros b it [].
- cbn. constructor.
- intros b [].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Theorem as0_art_rt_ia : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ia FSG (art_gs0 FSG gfs0 k0) FULL.
Proof.
intros FSG gfs0 k0. unfold art_rt_ia. cbn [art_gs0 g_ia g_qt g_qg].
repeat match goal with |- _ /\ _ => split end; try CL.
- intros H. discriminate H.
- intros _. split; reflexivity.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC"] Lemma var_in : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "K'R3'K'E'7&S4&QKvT>%211r3r2r1%744321(C%;3:21'D&T3&QOvLr4%3221%52<1%622<%8221p0:1pY:G1pYBH1pY0J1").
Proof.
intros e lo hi H. unfold is_var_in in H. destruct e; try discriminate.
apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC Hin) as HK. cbn [kentry_ok] in HK. unfold uE. lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH E R model HC"] Lemma img_zero4 : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q8'K'E'7&S2&QKvT>%211r3r2%63321(C%:3921&T3r4%2216&T0+4%22:1%6215&S<%8217r5%7216&S;%<221&Q<&SKvMr6u4z%6554321p081p0=1p0@1p0E1p0I1pXFQ51pY:Q61pYBQ71").
Proof.
intros lo hi a H H1 H2 H3 H4. unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
unfold cell.
assert (HN : forall x : word, a <= bv_unsigned x < a + Z.of_nat 4 -> FULL x = None).
{ intros x Hx. cbn in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
apply (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
unfold in_hull, DEP_LO, DEP_HI in *. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
pose proof (as0_dep_rdn_zero FULL 4%nat a H3 ltac:(cbn; lia) HN) as Hz. unfold ASEGS0 in Hz. rewrite Hz.
rewrite (wleb_zero 4 ltac:(lia)). reflexivity.
Qed.
Definition K0D : nat := 16384%nat.
Section SE.
Variables (FSG : Type).
Variables (gfs0 : FSG).
Theorem as0_art_rt_depot : art_rt_depot FSG rn (art_gs0 FSG gfs0 K0D) FULL.
Proof using sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 FSG gfs0.
unfold art_rt_depot, DInvD. cbn [art_gs0 g_depot as0_rn rn_l2 rn_blk]. unfold NID, STO, MAP1, DEP, apart.
exists 1, (uE E (tfE cs)), (uE E (stE cs)).
pose proof sp0_win as W. RG I_L2 0x100000. RG I_BLK 0x800000. RA I_L2 I_BLK 0x100000 0x800000.
destruct G as (l1 & l2 & l3 & l4 & l5 & l6). destruct G0 as (b1 & b2 & b3 & b4 & b5 & b6).
pose proof (var_in (tfE cs) 2 3 ltac:(chk)) as VT. pose proof (var_in (stE cs) 2 3 ltac:(chk)) as VS.
pose proof (cellW (ELit 0) 0x20cbc8 8 (tfE cs) ltac:(chk)) as X1. rewrite uE0 in X1.
pose proof (cellW (ELit 0) (0x20cbc8 + 24) 4 (stE cs) ltac:(chk)) as X2. rewrite uE0 in X2.
pose proof (cellW (ELit 0) 0x61cbe8 8 (bL2 cs) ltac:(chk)) as X3. rewrite uE0 in X3.
pose proof (cellW (ELit 0) (0x20cbc8 + 16) 8 (bBLK cs) ltac:(chk)) as X4. rewrite uE0 in X4.
pose proof (wrK (ELit 0) 0x21cbd8 4194308 ltac:(chk)) as W1. rewrite uE0 in W1.
pose proof (wrK (ELit 0) 0x20cbc8 32 ltac:(chk)) as W2. rewrite uE0 in W2.
pose proof (wrK (bL2 cs) 0 (2 ^ 20) ltac:(chk)) as W3. rewrite Z.add_0_r in W3.
pose proof (wrK (bBLK cs) 0 (2 ^ 23) ltac:(chk)) as W4. rewrite Z.add_0_r in W4.
change (uE E (bL2 cs)) with (rbase E cs I_L2) in *. change (uE E (bBLK cs)) with (rbase E cs I_BLK) in *.
unfold K0D. change (Z.of_nat 16384) with 16384.
repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try CL.
-
intros b Hb.
pose proof (cellW (ELit 0) B1 4 (e_at (kn cs) (ELit 0) B1 4) ltac:(chk)) as Y1. rewrite uE0 in Y1. pose proof (var_in (e_at (kn cs) (ELit 0) B1 4) 0 1 ltac:(chk)) as V1.
pose proof (cellW (ELit 0) B2 4 (e_at (kn cs) (ELit 0) B2 4) ltac:(chk)) as Y2. rewrite uE0 in Y2. pose proof (var_in (e_at (kn cs) (ELit 0) B2 4) 0 1 ltac:(chk)) as V2.
unfold B1, B2 in *.
destruct (Z.eq_dec b 320574) as [->|N1]; [eexists; split; [exact Y1 | lia]|].
destruct (Z.eq_dec b 945827) as [->|N2]; [eexists; split; [exact Y2 | lia]|].
exists 0. split; [|lia].
destruct (Z_lt_dec b 320574); [|destruct (Z_lt_dec b 945827)].
+ apply (img_zero4 DEP_LO 3497168); [chk | unfold DEP_LO; lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
+ apply (img_zero4 (3497168 + 4) 5998180); [chk | lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
+ apply (img_zero4 (5998180 + 4) DEP_HI); [chk | lia | unfold DEP_HI; lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
-
intros id Hid. assert (id = 1) by lia. subst id.
pose proof (cellW (bL2 cs) 16 8 (e_at (kn cs) (bL2 cs) 16 8) ltac:(chk)) as N1. pose proof (cellW (bL2 cs) 24 4 (ELit 0) ltac:(chk)) as N2. rewrite uE0 in N2.
change (uE E (bL2 cs)) with (rbase E cs I_L2) in *.
exists (uE E (e_at (kn cs) (bL2 cs) 16 8)), 0. pose proof (u64_range (edenot E (e_at (kn cs) (bL2 cs) 16 8))). unfold uE in *.
repeat split; try lia; [exact N1 | replace (rbase E cs I_L2 + 16 * 1 + 8) with (rbase E cs I_L2 + 24) by ring; exact N2].
Qed.
End SE.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHKL R model HC"] Theorem as0_art_rt_ghost : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ghost FSG rn (art_gs0 FSG gfs0 k0) FULL.
Proof.
intros FSG gfs0 k0. assert (C : cellA FULL (0x137970 + 72) 8 0xe666661) by CL.
unfold art_rt_ghost. cbn [art_gs0 g_qt g_qg g_cls app]. split; [intros b it []|]. split; [|split; [intros b []|exact C]].
intros c Hc. cbn [art_cls0 cl_au cl_mfa cl_cache length]. split; [intros X; exfalso; lia|]. pose proof (art_ic_mc_range c ltac:(lia)). cbn. lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_alloc_rep : forall (FSG : Type) (gfs0 : FSG), art_alloc_rep FSG rn (art_gs0 FSG gfs0 K0D) [] FULL.
Proof.
intros FSG gfs0. unfold art_alloc_rep.
exact (conj as0_art_run_ok (conj as0_art_rt_statics (conj as0_art_rt_thread (conj (as0_art_rt_primary FSG gfs0 K0D)
(conj (as0_art_rt_chunks FSG gfs0 K0D) (conj (as0_art_rt_sec FSG gfs0 K0D) (conj (as0_art_rt_quar FSG gfs0 K0D)
(conj (as0_art_rt_depot FSG gfs0) (conj (as0_art_rt_ia FSG gfs0 K0D) (conj (fun b (Hb : In b []) => match Hb with end) (as0_art_rt_ghost FSG gfs0 K0D))))))))))).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs R model HC"] Lemma byteZ : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q5'R3'K'E'7&R6&QKvT>%211r4r3r2%744321(C%;3:21'D&T3&T0&QOvLr5%3221%521=%721<&T4%823?%22?1%<241&R:vMz%332E1p051p0C1pXFQ01pYHQ11pYJQ21pXHQ41").
Proof.
intros b off n a H Ha. unfold byte_at.
destruct (hc_zero ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H) as (_ & _ & Hz).
replace a with (uE E b + off + (a - (uE E b + off))) by ring. apply Hz. lia.
Qed.
Definition KSH : Z := 0x7fff8000 + 8192 * (SPB / 65536).
Definition as0_EXTRA : list (Z * Z) := [(KSH, KSH + 2 ^ 34)].
Definition as0_A0x : list (Z * Z) := as0_A0 as0_EXTRA cs E.
#[using="Type"] Lemma as0_EXTRA_wf : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "3&Q@&RC%211").
Proof.
unfold A_wf, as0_EXTRA, KSH, page_size. constructor; [|constructor]. cbn [fst snd].
set (q := SPB / 65536).
replace (2147450880 + 8192 * q) with ((524280 + 2 * q) * 4096) by ring.
replace ((524280 + 2 * q) * 4096 + 2 ^ 34) with ((524280 + 2 * q + 4194304) * 4096) by ring.
rewrite !Z.mod_mul by lia. repeat split; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_vis_shadow_allowed := (ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QH'R3'K'E'7&S9vT>r4r3%43321(C%83721&T3&QOvLr5%3221%5219&T0%12<;r6%8271%4216%;241&T5r7%=2<1%9216+8%5221z%L3M21&T4%123B%F249r8%B21;&T8+2+Q?%3221%M251&R<&RAr9%3321:p051p0=1p0?1p0B1p0K1p0Q21p0Q91pYDQC1pXFQD1pYHQF1pXHQG1")) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_vis_shadow_allowed) 0%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_vis_shadow_allowed) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_vis_shadow_allowed) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_vis_shadow_allowed) 3%nat 0%nat).
Lemma vis_shadow_allowed : ltac:(sec_stmt2 constr:(SEC_T_vis_shadow_allowed) 4%nat 0%nat).
Proof using Type b n a m.
intros Hv H1 H2 H8 Hm Ha Hhi x [X1 X2].
unfold HeapIfaceA.S, HeapIfaceA.SB in X1, X2.
unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn.
pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat (Z_to_bv 64 x)) as (P1 & P2 & P3).
assert (Hx : 0 <= x < 2 ^ 64).
{ pose proof (Z.div_pos a 8 Ha ltac:(lia)). assert ((a + m - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
rewrite u64_lit in P1, P2 by exact Hx.
unfold as0_A0x, as0_A0, A0_of, page_allowedb. rewrite existsb_app. apply orb_true_iff. left.
apply existsb_exists. exists (pagedown (sh_lo ASAN0 E (b, n)), pageup (sh_hi ASAN0 E (b, n))). split.
- unfold allowA. apply in_flat_map. exists (b, n). split; [apply in_or_app; left; exact Hp|]. right. left. reflexivity.
- cbn [fst snd]. unfold sh_lo, sh_hi, page_size. cbn [fst snd shadow_off ASAN0].
assert (L1 : uE E b / 8 <= a / 8) by (apply Z.div_le_mono; lia).
assert (L2 : (a + m - 1) / 8 < (uE E b + uE E n) / 8).
{ pose proof (Z.div_mod (uE E b + uE E n) 8 ltac:(lia)) as D. rewrite H8 in D.
assert ((a + m - 1) / 8 <= (uE E b + uE E n - 1) / 8) by (apply Z.div_le_mono; lia).
assert ((uE E b + uE E n - 1) / 8 < (uE E b + uE E n) / 8); [|lia].
apply Z.div_lt_upper_bound; [lia|]. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End SE.
Variables BUDGET LENMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= JatInv.KMAX /\ 0 <= LENMAX < 2 ^ 62.
Hypothesis BUD_le : a_eager cs + a_abytes cs + 2 ^ 34 + BUDGET <= AsanInitK.LIMIT.
Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + JatInv.KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
#[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
#[local] Notation RESV0 := (segments_reserved ASEGS0).
#[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
Definition as0_BASEx : Z := as0_BASE as0_EXTRA cs.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHK0 R HC LENMAX BUD BUD_le GAP"] Theorem as0_art_binv : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "L&Q8&SK&Q5&Q2vTJ%211%411&Q0&S=%211&Q6%116&SJ&RKvLvT>%3221%511&RBv1(>'Q>%211&RAvM&Q1%11F%K<JEB@:98543F1").
Proof.
apply BINV_intro. unfold rn_HI. cbn [as0_rn as0_ar rn_ar ar_sptop].
assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
{ unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
exact (as0_binv_main sp brk0 rdraw argv envp uid hw fs Hsp Hva BUDGET LENMAX JatInv.KMAX BUD as0_EXTRA as0_EXTRA_wf cs CHK0 Hb GAP E R FULL model HC).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma as0_shdef : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "G'U1yR0%211&Q:&U2r1%2251%411&G'E'?y8%<11%311vMr2%211(2%116%:3631%<11p0>1pXFD1").
Proof.
assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
{ unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
pose proof (as0_binv_main sp brk0 rdraw argv envp uid hw fs Hsp Hva BUDGET LENMAX JatInv.KMAX BUD as0_EXTRA as0_EXTRA_wf cs CHK0 Hb GAP E R FULL model HC) as B.
intros a Ha. eapply bi_shdef; [exact B | exact Ha].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma byte1 : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q9'K'E'7&R4&QKvT>%211(R0z%211r2u1r1%611%;585431(C%?3>21'D&T3r3%22<1&T4&T8+2+R0%3221%5271%:271&Q:r5%211&R:vMr6%33215p051p091p0:1p0F1pZ:Q71pXFQ81").
Proof.
intros a v H Ha Hv Hs. pose proof (cellW (ELit 0) a 1 (ELit v) H) as X. rewrite uE0, (uE_lit E v Hv), Z.add_0_l in X.
unfold cell in X. rewrite (art_bytes1 v Hv) in X. cbn [rdn] in X. unfold byte_at.
pose proof (as0_shdef (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; exact Hs)) as D.
destruct (FULL (Z_to_bv 64 a)) as [b|]; [|contradiction]. injection X as ->. reflexivity.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma glob_ok : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "G'A'K%2211'E'7&RN&QKvT>%211r1%5221(C%93821&R=vM&:r2%23@@1&B%13BB3%73631p091pY2D1").
Proof.
intros [beg size] H. cbn [fst snd]. unfold glob_chk in H. cbn [fst snd] in H. chk_split H.
repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
assert (Q1 : 0x10000 / 8 <= beg / 8) by (apply Z.div_le_mono; lia). assert (Q2 : beg / 8 <= 0x691000 / 8) by (apply Z.div_le_mono; lia).
change (0x10000 / 8) with 8192 in Q1. change (0x691000 / 8) with 860672 in Q2.
assert (Q3 : 0 <= size / 8) by (apply Z.div_pos; lia). assert (Q4 : size / 8 <= 4096 / 8) by (apply Z.div_le_mono; lia). change (4096 / 8) with 512 in Q4.
pose proof (Z.mod_pos_bound size 8 ltac:(lia)) as Q5.
unfold shadow_blk, shadow_zero, HeapIfaceA.S, HeapIfaceA.SB. split.
- intros j Hj. apply (byteZ (ELit 0) (beg / 8 + 0x7fff8000) (size / 8)); [assumption | rewrite uE0; lia].
- intros NZ. apply byte1; [match goal with X : (if Z.eqb (size mod 8) 0 then true else ?c) = true |- ?c = true => destruct (Z.eqb_spec (size mod 8) 0) as [E0|_]; [exfalso; exact (NZ E0) | exact X] end
| lia | lia | unfold in_shadow_rw, LSH_LO, LSH_HI; left; lia].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 BUDGET LENMAX BUD BUD_le GAP"] Theorem as0_art_c_statics : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "7&S>&RKvLvT>%3221vM%6221").
Proof.
unfold art_c_statics. cbn [as0_rn as0_ar rn_tp rn_dtls]. unfold TP.
pose proof sp0_win as W.
pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
split; [repeat split; lia|].
split; [CL|]. split; [CL|]. split; [CL|].
split. { pose proof (cellW (ELit 0) (TP + 8) 8 (bD cs) ltac:(chk)) as X. rewrite uE0 in X. exact X. }
split. { pose proof (cellW (bD cs) 24 8 (ELit TP) ltac:(chk)) as X. rewrite (uE_lit E TP) in X by (unfold TP; lia). exact X. }
split.
{ intros x Hx. change (HeapIfaceA.S 0x10000) with 2147459072 in Hx. change (HeapIfaceA.S 0x23100) with 2147468832 in Hx. change (HeapIfaceA.S 0x238e0) with 2147469084 in Hx. change (HeapIfaceA.S 0x12cda0) with 2147604916 in Hx. change (HeapIfaceA.S 0x12ce40) with 2147604936 in Hx. change (HeapIfaceA.S 0x137140) with 2147610152 in Hx. change (HeapIfaceA.S 0x137640) with 2147610312 in Hx. change (HeapIfaceA.S 0x23120) with 2147468836 in Hx. change (HeapIfaceA.S 0x23160) with 2147468844 in Hx. change (HeapIfaceA.S 0x231e0) with 2147468860 in Hx. change (HeapIfaceA.S 0x23340) with 2147468904 in Hx. change (HeapIfaceA.S 0x691000) with 2148311552 in Hx.
destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
- apply (byteZ (ELit 0) 2147459072 9760); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147468836 8); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147468860 44); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147469084 135832); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147604936 5216); [chk | rewrite uE0; lia].
- apply (byteZ (ELit 0) 2147610312 701240); [chk | rewrite uE0; lia]. }
split; [|exact as0_shdef].
assert (HG : forallb (glob_chk (kn cs)) ART_GLOBALS = true) by chk.
apply Forall_forall. intros g Hg. exact (glob_ok g (proj1 (forallb_forall _ _) HG g Hg)).
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 BUDGET LENMAX BUD BUD_le GAP"] Theorem as0_art_fsinv : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "=&SB&SA&RKvLvT>%3221&S@(>&R;%211vM%:565221p0<1").
Proof.
intros FSH. apply FSH; cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs]; unfold TP.
-
unfold art_fs_geo, rn_HI, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES. cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs ar_sptop]. unfold TP.
pose proof sp0_win as W. RG I_FAKE 0xb09000. RA I_FAKE I_THREAD 0xb09000 4096. RG I_THREAD 4096.
destruct G as (f1 & f2 & f3 & f4 & f5 & f6). specialize (f6 ltac:(unfold I_FAKE; lia)).
pose proof (xpos (bF cs) ltac:(chk)) as PF. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
repeat split; lia.
- pose proof (wrK (bF cs) 0 0xb09000 ltac:(chk)) as W. rewrite Z.add_0_r in W. exact W.
- pose proof (cellW (ELit 0) TP 8 (bF cs) ltac:(chk)) as X. rewrite uE0 in X. exact X.
- exact (cellW (bT cs) 72 8 (bF cs) ltac:(chk)).
- pose proof (cellW (bF cs) 88 8 (ELit 20) ltac:(chk)) as X. rewrite (uE_lit E 20) in X by lia. exact X.
- intros a Ha Hn. change (rbase E cs I_FAKE) with (uE E (bF cs)) in *.
destruct (Z_lt_dec a (uE E (bF cs) + 88)).
+ apply (byteZ (bF cs) 0 88); [chk | lia].
+ apply (byteZ (bF cs) 96 (4096 + 32768 - 96)); [chk | lia].
- exact as0_art_c_statics.
Qed.
#[using="LENMAX BUD_ge GAP"] Theorem as0_art_credit : forall (FSG : Type) (gfs0 : FSG), art_credit_ok FSG BUDGET rn (art_gs0 FSG gfs0 K0D) [] (8192, 2 ^ 34).
Proof.
intros FSG gfs0. unfold art_credit_ok, art_nret, art_nq, JatInv.KMAX, K0D.
cbn [art_gs0 g_log g_sec g_depot g_cls g_qt g_qg app fst snd length art_cost_sum fold_right art_live fold_left].
unfold art_cls0. cbn [cl_mu cl_free cl_cache length]. change (Z.of_nat 0) with 0. change (Z.of_nat 16384) with 16384.
repeat split; try lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R model HC HGEO_STK HSP16 HSPA BUDGET LENMAX GAP"] Theorem as0_art_client : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "?&SC&RKvLvT>%3221(>'A'K%2211%411&R;%611&RAvM%>6:53321").
Proof.
unfold art_client_ok. cbn [as0_rn as0_ar rn_ar ar_sptop ar_fs ar_stack_top ar_stack_bottom map].
pose proof sp0_win as W. destruct HGEO_STK as (S1 & S2 & S3 & S4 & S5).
pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
pose proof (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UT. pose proof (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UL.
pose proof (utop_bounds E) as UB.
repeat match goal with |- _ /\ _ => split end; try lia.
- intros b [].
- constructor.
-
apply (vis_shadow_allowed e_top e_stk_len); [chk | lia | lia | rewrite UT, UL; replace (utop E + (2 ^ 47 - utop E)) with (2 ^ 47) by ring; reflexivity | lia | lia | lia].
-
RG I_FAKE 0xb09000. destruct G as (f1 & f2 & f3 & f4 & f5 & f6).
apply (vis_shadow_allowed (bF cs) (ELit 0xb09000)); change (uE E (bF cs)) with (rbase E cs I_FAKE); rewrite ?(uE_lit E 0xb09000) by lia; unfold FS_BYTES; try lia; [chk|].
pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)) as D. rewrite f1 in D.
replace (rbase E cs I_FAKE + 11571200) with ((512 * (rbase E cs I_FAKE / 4096) + 1446400) * 8) by lia. apply Z.mod_mul. lia.
-
apply (vis_shadow_allowed (ELit 0x10000) (ELit 0x681000)); rewrite ?(uE_lit E 0x10000), ?(uE_lit E 0x681000) by lia; try lia; [chk | reflexivity].
Qed.
Hypothesis CHKZ : art_lazy_chk cs = true.
#[local] Notation PARR := (rbase E cs I_PARR).
#[local] Notation BLKB := (rbase E cs I_BLK).
#[local] Notation RIS := (SPB + 2 ^ 37).
#[using="CHKZ"] Lemma lazy_parts : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "R:'F'<'QJ%211'D'E&QDvT>%211&6r2(8(QB&RD%117(R0+TP0%211%6241r1%93B21%<3C;1%A3C>1'7&SO&RO%11C%33I1A(C%H3621&S0%11H%83N1H%L3:15'A'R3%2211&5&S8&QK%11Q1%321F&S6%12Q4H%7231qYL91&QF%11Q8&QC%11Q:%Q93>31%K3?61%Q?3M1H&T3+<&R1&RL%11QB%32B1%6251&S9+XPPP0%Q?11%33QH61%QK3Q91Q4%QM261%QN2>1%QO2Q21%R02Q71%R12Q?1qY8R31%R72R41qY6R51%R92R61").
Proof.
pose proof CHKZ as H. unfold art_lazy_chk in H.
apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
destruct (hsplit (E_RISX cs) (a_hlz cs)) as [[h1 h2]|] eqn:Hs; [|discriminate].
exists h1, h2. split; [exact (hsplit_eq _ _ _ _ Hs)|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
split; [apply Z.leb_le; exact C4 | exact C5].
Qed.
#[using="Type"] Lemma is_rng_sound : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q7'R3'K'E'7&S3r4r3r2r1%544321(C%93821'D&T3z%2218&T4&T8+2+R0%3221%52>1%:271&QOvLr6%3221%423F%J3K21r5%7261%M3N1I%D241p0;1p0G1pQNQ21pXJQ41pYHQ51pXHQ61").
Proof.
intros b n b0 L H HL. unfold is_rng in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst.
split; [reflexivity | apply uE_lit; exact HL].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP"] Lemma ris_val2 : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "D'E'K&QOvL&RDvT>%211%5241&T0&RM%115%9281+RPP0%5221&T8+2+Q5%3221%:251%C3B<1").
Proof.
unfold E_RISX, uE. cbn [edenot]. rewrite u_add64. cbn [edenot]. rewrite (u64_lit 0x2000010000) by lia.
pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _).
pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
unfold uE in *. rewrite Z.mod_small by lia. lia.
Qed.
#[using="CHK0"] Lemma hlz_ok : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK ";'E'7&R7&QEvT>%211&QD%113%6231(C%:3921").
Proof. pose proof CHK0 as H. unfold as0_chk in H. repeat (apply andb_prop in H as [H ?]). assumption. Qed.
Section SE.
Local Abbreviation SEC_T_lazy_piece := (ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "RC'A'U1yR0%211%4211&SMr1&Q1vTJ%211%53641'K&U2&:r2%23<<1%42>1&T0r3%63@@1%82B1&B%13CC4%;2E1%7241'D'H&T3&R8vLvT>&RE%43321%621C+XPPP0%B231%92N1%<241&RG%;3:91%=21J%H227%?2Q41%B231&RF%A3@?1%C21Q0+TPPPRTP0%O231%F2Q;1%I241+QoonlP0%I21Q6+`PQoooPP0%K2Q@1%N231%N261%O2>1%Q02E1&QO&RM%11O%32Q11+RPP0%Q?221&T8+2+Q5%3221%QD251%Q;2R01+TP0%QG231%Q>21QK%Q@241&T4%12QNR6%QD231%QE2D1tY0R4QG1tXHR5R01p0R71pYNR>1")) (only parsing).
Variable q : ltac:(sec_ty2 constr:(SEC_T_lazy_piece) 0%nat 0%nat).
Lemma lazy_piece : ltac:(sec_stmt2 constr:(SEC_T_lazy_piece) 1%nat 0%nat).
Proof using sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ q.
intros Hq.
cbv zeta. rewrite (hb_lazy ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) in Hq.
destruct lazy_parts as (h1 & h2 & Hsplit & Hpre & Hzone & _).
pose proof (hl_hops_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (a_hlz cs) HC nofog hlz_ok) as WF.
destruct (hl_replay E (a_hlz cs) WF q Hq) as (P1 & P2 & b & n & Hb & P3 & P4).
split; [|split; [|lia]].
- pose proof (proj1 (forallb_forall _ _) Hzone (HCons b n) Hb) as Hz. cbn [hop_zone] in Hz.
repeat (apply orb_prop in Hz as [Hz|Hz]).
+ destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. left. change (uE E (bBLK cs)) with BLKB in E1. lia.
+ destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. left. change (uE E (bP cs)) with PARR in E1. lia.
+ destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. right. left. change (uE E (bKS cs)) with KB in E1. lia.
+ destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x7fff7000) in E1 by lia. right. right. right. lia.
+ destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x8fff7000) in E1 by lia. right. right. right. lia.
+ destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x2008fff7000) in E1 by lia. right. right. right. lia.
- rewrite Hsplit in Hq, WF.
pose proof (hl_replay_sub E h1 (E_RISX cs) (ELit 4096) h2 WF) as SUB. rewrite ris_val2, (uE_lit E 4096) in SUB by lia.
apply SUB; [|exact Hq]. intros b' n' Hin.
pose proof (proj1 (forallb_forall _ _) Hpre (HCons b' n') Hin) as Hp. cbn [hop_pre] in Hp.
destruct HGEO_SPB as ((K1 & K2) & _).
apply orb_prop in Hp as [Hp|Hp]; destruct (is_rng_sound _ _ _ _ Hp ltac:(lia)) as [E1 E2]; rewrite E1, E2.
+ change (uE E (bBLK cs)) with BLKB.
destruct (ra I_BLK I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
+ change (uE E (bP cs)) with PARR.
destruct (ra I_PARR I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
Qed.
End SE.
#[using="Type"] Lemma pb_facts : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "J'U1yR0%211'D&T3&U2&Q3r1%211%4281%5293%7221&T4&T0+TP0%2261%4261%>261'E'K&T5%12<7z%53421%E271pZ>G1").
Proof.
intros x. pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat x) as (P1 & P2 & P3). auto.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma as0_lazy_c1 : forall (FSG : Type) (gfs0 : FSG) (k0 : nat) (w : word),
page_in_ranges (page_base w) (m_vm_lazy model) = true -> art_lazy_zone FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w).
Proof.
intros FSG gfs0 k0 w Hl. destruct (hl_page_piece w _ Hl) as (q & Hq & Q1 & Q2).
destruct (pb_facts w) as ((P1 & P2) & _). destruct (lazy_piece q Hq) as (Hz & Hr & _). cbv zeta in Hz, Hr.
destruct HGEO_SPB as ((K1 & K2) & _).
assert (NC : ~ (RIS <= bv_unsigned w < RIS + 4096)) by lia.
assert (NCOM : ~ art_committed FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w)).
{ unfold art_committed, rn_ris, rn_spb. cbn [as0_rn as0_ar rn_ar rn_qs ar_space_beg art_gs0 g_cls g_sec_committed]. unfold art_cls0. cbn [cl_mu cl_mfa].
rewrite spb_qs. intros [X|[(c & _ & [X|X])|(X & _)]]; [exact (NC X) | lia | lia | discriminate X]. }
unfold art_lazy_zone. cbn [as0_rn as0_ar rn_ar rn_blk rn_kbase rn_parr]. change (2 ^ 23) with 0x800000.
destruct Hz as [Z|[Z|[Z|Z]]].
- right. left. lia.
- right. right. split; [right; lia | exact NCOM].
- right. right. split; [left; lia | exact NCOM].
- left. lia.
Qed.
#[using="cs E BUDGET LENMAX GAP"] Lemma win_nolazy : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QI'K'E&T5r2+TP0%3221z%63721'A'U1yR0%211%4211&SMr1&Q1vTJ%211%53641'H&T3&T0&U2&:%13==E%32?1&B%13@@H%62B1%8241r6%;221r5%=218%?231p0A1pYNH1'D%@2LH%C291&T4%1239%5231'7&Q4&Q3%11Q;%321N(9%Q@3621p081pZ>Q81p0@1p0Q>1p0Q?1pY:QG1pYBQH1").
Proof.
intros lo hi Hlo Hhi Hap x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:Hl; [exfalso | reflexivity].
destruct (hl_page_piece x _ Hl) as (q & Hq & Q1 & Q2). destruct (pb_facts x) as ((P1 & P2) & P3).
pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
destruct (Hap q Hq) as [X|X]; lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC BUDGET LENMAX GAP"] Lemma apx_sound : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QF'R3'K'A%1233'E'7&RI&QKvT>%211r3r2r1%744321(C%;3:21'D&T3z%2219&T4&T8+2+R0%3221%52?1%:271'H&T0&QOvLr5%3221r4%6221&:%13Q4Q4J%8271%E241&B%13Q8Q8N%<2;1%>251%J21;%A261%I2K4%M24F%O221%Q0241p0G1p0Q31pYLQ@1pZHQC1pZBQE1").
Proof.
intros zb zn p H Hzn. unfold apx in H. destruct (split_lit zb) as [zb' zk] eqn:Hz. destruct (split_lit (fst p)) as [pb pk] eqn:Hp.
apply andb_prop in H as [H Hap]. apply andb_prop in H as [Fz Fp].
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (flat_x_sound ASEGS0 E _ (kn cs) zb' zk (ELit zn) HK Fz) as (A1 & A2 & A3).
pose proof (flat_x_sound ASEGS0 E _ (kn cs) pb pk (snd p) HK Fp) as (B1 & B2 & B3).
pose proof (split_lit_denot E _ zb' zk Hz) as Dz. pose proof (split_lit_denot E _ pb pk Hp) as Dp.
cbn [edenot] in A2, A3. rewrite (u64_lit zn) in A2, A3 by lia.
assert (Ez : uE E zb = estart E (SA zb' zk)).
{ unfold uE. rewrite Dz. unfold estart in *; cbn [a_base a_off] in *. rewrite u64_lit by lia. reflexivity. }
assert (Ep : uE E (fst p) = estart E (SA pb pk)).
{ unfold uE. rewrite Dp. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
pose proof (ranges_apart_x_sound ASEGS0 E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
unfold elenZ in D. cbn [edenot] in D. rewrite (u64_lit zn) in D by lia. rewrite <- Ez, <- Ep in D.
split; [exact D|]. split; [exact B3|]. rewrite Ep. unfold uE. lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC BUDGET LENMAX GAP"] Lemma vis_hi_sound : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q0'A'R3%2211'E'7&S8&QKvT>%211r1%5221(C%93821&T3&T0&QOvL&:r2%23BB1%5241&B%13EE4%8271%:241&T8+2+Q?%3221%@251p0B1pYLM1").
Proof.
intros p H. unfold vis_hi in H. apply orb_prop in H as [H|H].
- apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. rewrite H1, H2.
pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
rewrite (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP), (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP). lia.
- destruct (xhi (kn cs) (fst p)) as [hi|] eqn:Hx; [|discriminate]. destruct (snd p) as [n| | | | | | |] eqn:Hn; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
pose proof (xhi_sound ASEGS0 E _ (kn cs) (fst p) hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as X.
unfold uE. cbn [edenot]. rewrite (u64_lit n) by lia. lia.
Qed.
#[using="cs E BUDGET LENMAX GAP"] Lemma round_apart : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q3'K'E&T5r2+TP0%3221z%63721'H&T3r3r6%3221&T0r5%2241r4%8221%:261&QMr7%211%=261&QN%;24=%211%A21<%C251p0:1p0F1p0G1pZDO1pZFQ01pYHQ11pXHQ21").
Proof.
intros b n zl zh Hl Hh Hap. unfold pagedown, pageup.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct Hap as [X|X]; [left | right]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="cs E BUDGET LENMAX GAP"] Lemma round_al : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "F'K'D'E&T5&QMr1%211+TP0%5221z%83:21&QN%117%:216%<3>15&T3%12:;%22<5%A221%B251%C2:1pZ@E1").
Proof.
intros z. unfold pagedown, pageup. rewrite !Z.mod_mul by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
repeat split; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="cs E BUDGET LENMAX GAP"] Lemma round_id : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "C'K'E&T5r1+TP0%3221z%63721'D&QMr2%211%;3<12&QN%114%>3?15%8241p0:1pZ@B1").
Proof.
intros z Hz. unfold pagedown, pageup.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Section SE.
Local Abbreviation SEC_T_own_window := (ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "R6'A'R3%2211&SMr1&6&QFvT>%211&QC%113%63931%93:81'K&QM&QOvL&:r2%23BB1%5241%711&QN&T0r3%83HH1%;2:1&B%13KK4%>2=1%7241%911'H'D&T3&R8&RE%23EN1%421D+XPPP0%A231%72Q51%9241'U1yR0%211&U2%123Q;%>2H1&T4%123Q0%B231'E'7&Q4&Q3%11Q6&Q1vTJ%211%6241(9%:3921p0<1pZ>C1%Q12G1tY:QEQ31tYBQFQ>1p0QH1pYLR31")) (only parsing).
Variable p : ltac:(sec_ty2 constr:(SEC_T_own_window) 0%nat 0%nat).
Lemma own_window : ltac:(sec_stmt2 constr:(SEC_T_own_window) 1%nat 0%nat).
Proof using sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ p.
intros Hp.
cbv zeta. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & HalB & _).
pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [_ Hown].
pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
destruct HGEO_SPB as ((K1 & K2) & K3).
unfold own_ok in Hown. apply orb_prop in Hown as [Hown|Hown]; [apply orb_prop in Hown as [Hown|Hown]|].
-
destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2. change (uE E (bBLK cs)) with BLKB.
destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
left. rewrite R1, R2. lia.
-
destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2, ris_val2.
assert (RA4 : RIS mod 4096 = 0).
{ pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. replace RIS with ((16 * (SPB / 65536) + 33554432) * 4096) by lia. apply Z.mod_mul. lia. }
destruct (round_id RIS RA4) as [R1 _]. destruct (round_id (RIS + 4096) ltac:(rewrite Z.add_mod, RA4 by lia; reflexivity)) as [_ R2].
right. rewrite R1, R2. apply win_nolazy; [exact RA4 | rewrite Z.add_mod, RA4 by lia; reflexivity |].
intros q Hq. destruct (lazy_piece q Hq) as (_ & Hr & _). exact Hr.
-
apply andb_prop in Hown as [Hown HB]. apply andb_prop in Hown as [HK HP].
destruct (apx_sound _ _ _ HK ltac:(lia)) as (AK & NPOS & NW). destruct (apx_sound _ _ _ HP ltac:(lia)) as (AP & _ & _).
change (uE E (bKS cs)) with KB in AK. change (uE E (bP cs)) with PARR in AP.
set (b := uE E (fst p)) in *. set (n := uE E (snd p)) in *.
destruct (round_al b) as (L1 & _ & L3). destruct (round_al (b + n)) as (_ & H2 & H3).
pose proof CHK0 as C0. unfold as0_chk in C0. repeat (apply andb_prop in C0 as [C0 ?]).
match goal with Hf : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true |- _ =>
pose proof (proj1 (forallb_forall _ _) Hf p Hp) as Hband end.
assert (ABAND : b + n <= 0x7fff7000 \/ 0x10007fff8000 <= b).
{ pose proof (hl_off_band ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model p) as OB.
destruct (Z_lt_le_dec b 0x7fff7000) as [Hlt|Hge].
- left. destruct (Z_lt_le_dec 0x7fff7000 (b + n)) as [Hin|]; [exfalso | lia].
apply (OB 0x7fff7000 HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia].
- right. destruct (Z_lt_le_dec b 0x10007fff8000) as [Hin|]; [exfalso | lia].
apply (OB b HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia]. }
assert (ABLK : (b + n <= BLKB \/ BLKB + 0x800000 <= b) \/ (BLKB <= b /\ b + n <= BLKB + 0x800000 /\ b mod 4096 = 0 /\ n = 4096)).
{ apply orb_prop in HB as [HB|HB].
- destruct (apx_sound _ _ _ HB ltac:(lia)) as (AB & _ & _). change (uE E (bBLK cs)) with BLKB in AB. left. fold b n in AB. lia.
- apply andb_prop in HB as [HB1 HB2]. apply expr_eqb_eq in HB1. apply Z.leb_le in HB2.
assert (N4 : n = 4096) by (unfold n; rewrite HB1; apply uE_lit; lia).
destruct (ealign_sound ASEGS0 E _ (kn cs) (fst p) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as ((EA1 & EA2) & EA3).
assert (B4 : b mod 4096 = 0).
{ unfold b, uE. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ ealign (kn cs) (fst p))); [|exact EA3].
exists (2 ^ (ealign (kn cs) (fst p) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
pose proof (Z.div_mod b 4096 ltac:(lia)) as D1. pose proof (Z.div_mod BLKB 4096 ltac:(lia)) as D2. rewrite B4 in D1. rewrite b1 in D2.
destruct (Z_lt_le_dec b BLKB); [left; left; lia|]. destruct (Z_lt_le_dec b (BLKB + 0x800000)); [right; (clear - ABAND AK AP B4 BUDGET D1 D2 E GAP H3 HB2 HGEO_STK K1 LENMAX N4 b b2 cs g2 g4 l l0 n p p2 p4; lia) | left; right; (clear - BUDGET E GAP LENMAX b cs l0 n p; lia)]. }
destruct ABLK as [ABLK|(I1 & I2 & I3 & I4)].
+ right. apply win_nolazy; [exact L1 | exact H2 |].
intros q Hq. destruct (lazy_piece q Hq) as (Hz & _ & Hne). cbv zeta in Hz, Hne.
destruct Hz as [Z|[Z|[Z|Z]]].
* destruct (round_apart b n BLKB (BLKB + 0x800000) b1 ltac:(rewrite Z.add_mod, b1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
* destruct (round_apart b n PARR (PARR + 0x800000) p1 ltac:(rewrite Z.add_mod, p1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
* destruct (round_apart b n KB (KB + 0x2000011000) g1 ltac:(rewrite Z.add_mod, g1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
* destruct (round_apart b n 0x7fff7000 0x10007fff8000 ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
+ left. destruct (round_id b I3) as [R1 _]. destruct (round_id (b + n) ltac:(rewrite I4, Z.add_mod, I3 by lia; reflexivity)) as [_ R2].
rewrite R1, R2. lia.
Qed.
End SE.
#[using="Type"] Lemma vis_in_In : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "J'R3'E'7&S9vT>r2r1%43321(C%83721&SM'A%12<<(@r3%24??1:&6&QF%11>&QC%11@%53931%<3:71p0>1pYHH1pXHI1").
Proof.
intros b n Hv. unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn. apply in_or_app. left. exact Hp.
Qed.
#[using="cs E BUDGET LENMAX GAP"] Lemma win_allowed : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q?'<'A'K%2211%411'U1yR0%211&SM(@r3r2%34::21r4%63;21'E&T5+TP0%2251z%53B21'D&T3r6&U2%12C<%4231&T4r5%2241%9241'7&QAr8&Q3%117%4231(C%G3721p091p0D1p0E1p0L1pZ>Q41pY:Q:1pYBQ;1p2Q:1").
Proof.
intros A lo hi x Hin Hlo Hhi Hx. unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. unfold page_size.
destruct (pb_facts x) as ((P1 & P2) & P3).
pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Section SE.
Variables (FSG : Type).
Variables (gfs0 : FSG).
Theorem as0_art_lazy_ok : art_lazy_ok FSG rn (art_gs0 FSG gfs0 K0D) as0_A0x (m_vm_lazy model).
Proof using sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ FSG gfs0.
unfold art_lazy_ok. cbn [as0_rn as0_ar rn_ar rn_blk rn_qs]. change (2 ^ 23) with 0x800000.
pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3).
pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
split; [exact (as0_lazy_c1 FSG gfs0 K0D)|]. split; [|split].
-
intros w Hw. unfold as0_A0x, as0_A0, A0_of in Hw. apply in_app_or in Hw as [Hw|Hw].
+ unfold allowA in Hw. apply in_flat_map in Hw as (p & Hp & Hwp). unfold allow1 in Hwp. destruct Hwp as [<-|[<-|[]]]; cbn [fst snd].
* destruct (own_window p Hp) as [X|X]; [right; left; exact X | right; right; exact X].
* left. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & _).
pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [Hhi _]. apply vis_hi_sound in Hhi.
unfold sh_lo, sh_hi. cbn [shadow_off ASAN0]. pose proof (u64_range (edenot E (fst p))) as U1. pose proof (u64_range (edenot E (snd p))) as U2. unfold uE in *.
unfold pagedown, pageup.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
+ unfold as0_EXTRA in Hw. destruct Hw as [<-|[]]. cbn [fst snd]. left. unfold KSH.
pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. lia.
-
intros x Hx. apply (win_allowed as0_A0x KSH (KSH + 2 ^ 34)).
+ unfold as0_A0x, as0_A0, A0_of. apply in_or_app. right. left. reflexivity.
+ unfold KSH. replace (2147450880 + 8192 * (SPB / 65536)) with ((524280 + 2 * (SPB / 65536)) * 4096) by ring. apply Z.mod_mul. lia.
+ unfold KSH. replace (2147450880 + 8192 * (SPB / 65536) + 2 ^ 34) with ((524280 + 2 * (SPB / 65536) + 4194304) * 4096) by ring. apply Z.mod_mul. lia.
+ unfold KSH. lia.
-
intros x Hx. destruct lazy_parts as (_ & _ & _ & _ & _ & _ & _ & Hvin).
apply (win_allowed as0_A0x BLKB (BLKB + 0x800000)); [| exact b1 | rewrite Z.add_mod, b1 by lia; reflexivity | lia].
unfold as0_A0x, as0_A0, A0_of. apply in_or_app. left. unfold allowA. apply in_flat_map. exists (bBLK cs, ELit 0x800000).
split; [exact (vis_in_In _ _ Hvin)|]. unfold allow1. cbn [fst snd]. left.
rewrite (uE_lit E 0x800000) by lia. change (uE E (bBLK cs)) with BLKB.
destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
rewrite R1, R2. reflexivity.
Qed.
End SE.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC BUDGET LENMAX GAP"] Lemma role_kn : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "R9'='K&Jr4uA%3221'E'7&S5vT>r5%33218(C%73621'D&T3z%2217&T4&T8+2+R0%3221%52=1%:271&R8vLr7%332C1%>21C&T0r6%221Fr8%938I1%5218%E241'F'A%12Q6Q6&SMr1&Q9&Q5&Q2vTJ%211%411&Q0&S=%211%9241%<3=;1&:%13QEQE=%Q821F%J2GM&B%13QIQIA%Q<231%Q>251%Q?291qYNG1%J2H1p0L1p0Q41p0Q:1p0QF1p0QO1pYHR41pXFR51pQNR61pY<R81").
Proof.
intros i L a n Hi HL HLr Ha Hn. exists (ivZ (amap_den E (role cs i))). split.
- unfold KN0. apply in_map. apply in_or_app. right.
rewrite (hb_maps ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC nofog). apply in_map. apply role_in. rewrite len17. exact Hi.
- unfold lit_len in HL. apply expr_eqb_eq in HL. pose proof (role_lit E cs i L HL HLr) as El.
unfold ivZ, amap_den. cbn [fst snd]. unfold rbase, rlen, uE in *. lia.
Qed.
#[using="cs E BUDGET LENMAX GAP"] Lemma seg_kn : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "QK'K&SM'A'U1yR0%211%4211(@&U0r2%2261r1%4281%648831&Q0&S=%211%@3;41'D&T3zr3%3221&T4&T8+2+R0%3221%5271%;271'F%M2OO&Q9&Q5&Q2vTJ%211%411%621F%Q638L1&:%13Q9Q9Nr6%H221&T0r5%2241&B%13Q@Q@Q5%N231%Q0271%Q12<1qYNE1%G2F1p0I1p0J1p0Q71pZ8QI1pXHQJ1").
Proof.
intros b sz Hin Hb Hs. exists (ivZ (Z_to_bv 64 b, Z_to_bv 64 sz)). split.
- unfold KN0. apply in_map. apply in_or_app. left. exact Hin.
- unfold ivZ. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC BUDGET LENMAX GAP"] Theorem as0_art_kn_ok : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK ">&SF&Q5&Q2vTJ%211%411&Q0&S=%211&RKvLvT>%3221%=3851").
Proof.
unfold art_kn_ok, art_objs. cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_kbase rn_parr rn_l2 rn_blk rn_dtls ar_fs]. unfold FS_BYTES.
change (2 ^ 23) with 0x800000. change (2 ^ 20) with 0x100000.
intros o Ho.
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_THREAD 4096); [IDX | chk | lia | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_CTX 0x10000); [IDX | chk | lia | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_KSPACE 0x2000011000); [IDX | chk | lia | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_PARR 0x800000); [IDX | chk | lia | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_L2 0x100000); [IDX | chk | lia | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_BLK 0x800000); [IDX | chk | lia | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_FAKE 0xb09000); [IDX | chk | lia | lia | lia]|].
rewrite asan0_res_eq.
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
destruct Ho as [<-|[]]. cbn [fst snd]. apply (role_kn I_DTLS 4096); [IDX | chk | lia | lia | lia].
Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHK0 R FULL HC BUDGET LENMAX BUD BUD_le GAP"] Lemma as0_art_eager : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK ";&SD(>'A'K%2211%411&RA&Q1vTJ%211%:3541").
Proof. split; [eapply BINV_awf; exact as0_art_binv | intros b x []]. Qed.
#[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R HC HGEO_SPB HGEO_STK HSP16 HSPA LENMAX BUD BUD_le BUD_ge GAP CHKZ"] Theorem as0_art_handoff : ltac2:(TCodec.tc2 tcn__Ja0ArtHandoffK "Q1&SB&SE'S?&Q5&Q2vTJ%211%411&Q0&S=%211&Q6%116&RBv1&SA&RKvLvT>%3221&S@&R@+XP0&T8+2+Q2%3221&RAvM&R>%11I%N?MHECBA@<;:95431p0Q01").
Proof.
intros FSH. unfold art_handoff_target, vml_of. cbn [fst snd].
exact (conj (as0_art_alloc_rep art_fsg art_fsg0) (conj (as0_art_fsinv FSH) (conj as0_art_binv (conj (as0_art_credit art_fsg art_fsg0) (conj as0_art_client (conj as0_art_kn_ok (conj (as0_art_lazy_ok art_fsg art_fsg0) as0_art_eager))))))).
Qed.
End Derive.
