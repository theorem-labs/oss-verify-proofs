(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3Sound L5Defs L5Core L5CoreKit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmStep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Specif."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK.Kit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2I"]; ["2and"; "2eq"; "2not"; "2or"; "3sumbool"; "4Z"; "0HI"; "0K"; "0L"; "0LB"; "0LB2"; "0LBc"; "5Segment"; "6fetch_word"; "6is_ecall"; "7Model"]; ["7VmMaps"; "7m_halted"; "7m_vm_lazy"; "7m_vmmaps"; "8decode_any"; "9Jalr"; "9instr"; ":bvmap"; "0M"; "0M'"; "0M0"; "0M1"; "0M2"; "0M3"; "0P"; "0Q"]; ["0R"; "0R'"; "0R1"; "0R2"; "0R3"; ";msteps"; "<client_addr"; "<credit"; "<heap_pres_core"; "<hi_heap"; "<hl_sptop"; "<hl_stack"; "<in_errno"; "<regs_preserved"; "<stack_ok"; "=hpres"]; ["=stk"; "?defined"; "?outside"; "?range"; ">SCFG"; "Acfg"; "Acwr"; "Adk"; "Aek"; "AinW"; "@cs_all"; "BFPState"; "Bgetr"; "Bmkst"; "Bseg_rom"; "CTSet"]; ["Dsrealizes"; "Emem_grows"; "0SCFG_P"; "FIn"; "Fincl"; "Gadd"; "Gland"; "Gle"; "Glt"; "Gmodulo"; "Gof_nat"; "Gpow"; "Gsub"; "0VM"; "0W"; "0W'"]; ["0W1"; "0W2"; "0a"; "0b"; "0cr"; "0fx"; "0fx1"; "0hi"; "0k"; "0lo"; "0model"; "0n"; "0pc"; "0pc1"; "0r"; "0scr"]; ["0scr'"; "0scr2"; "0segs"; "0sp"; "0sp'"; "0sp2"; "HBV"; "HZ_to_bv"; "Hbv"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMK.
Ltac keep_arith := lazymatch goal with |- _ => L5FastLia.prune_arith end.
Ltac clear_disj_but H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end.
Ltac alia0 := first [ lia | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Ltac alia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | alia0 ].
Ltac feed_concl T := lazymatch T with ?A -> ?B => feed_concl B | _ => T end.
Ltac feed P tac :=
let T := type of P in
lazymatch T with
| ?A0 -> _ =>
let C := feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (apply P; clear P; first [ tac | lazymatch goal with |- ?A => fail 1 "feed: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P
| _ => idtac
end.
Ltac greg :=
lazymatch goal with |- getr ?R ?x = ?rhs =>
match goal with H : getr R ?y = ?rhs' |- _ =>
first [ constr_eq x y | replace x with y by (apply bv_eq; vm_compute; reflexivity) ];
first [ exact H
| lazymatch rhs with Z_to_bv 64 ?z => lazymatch rhs' with Z_to_bv 64 ?z' => replace z with z' by (clear; lia); exact H end end ]
end
end.
Ltac gmem :=
lazymatch goal with
| |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.u32_at ?sg ?M ?a ?v => match goal with H : L5.u32_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.u8_at ?sg ?M ?a ?v => match goal with H : L5.u8_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b ?m |- _ => apply (L5.defined_sub M b m a n H); clear; lia end
| |- L5.writable ?sg ?M ?a ?n => match goal with H : L5.writable sg M ?b ?m |- _ => apply (L5.writable_sub sg M b m a n H); clear; lia end
| |- L5.img_clear ?M ?lo ?hi => match goal with H : L5.img_clear M ?lo' ?hi' |- _ => first [exact H | (intros ? ?; apply H; clear - H; lia)] end
end.
Ltac arith_shape :=
lazymatch goal with
| |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
| |- @eq Z _ _ => idtac | |- (_ \/ _) => idtac | |- (~ _)%type => idtac | |- (_ /\ _) => idtac
| |- le _ _ => idtac | |- lt _ _ => idtac | |- @eq nat _ _ => idtac
end.
Ltac arith_goal := first [ arith_shape | red; arith_shape ].
Ltac sc0 := first [ assumption | greg | gmem | arith_goal; first [assumption | alia] ].
Ltac xfer AG C :=
first [ eapply L5C.u64_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
| eapply L5C.u8_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
| eapply L5C.defined_agree; [intros ? ?; apply AG; alia | exact C] ].
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index : ltac2:(TCodec.tc2 tcn__PmStep "N&Q7y5'SHyR0%211%5241'9&RCr1&R:%33421'A&R<r3&SG&RJr2%211%42A1%7261r4%9213%;3B31p0=1pVBB1&QM%12=:p031pS4G1pS2H1").
Proof. intros R R'.
intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmStep "N&Q7y5'SHyR0%211%5241'9&QMr3r2%3221&RC&R:%23741'A&R<r4&SG&RJ%11;%32C1%6251r5%8213%:3D31p0<1p0@1pVBE1pS4G1pS2H1")) (only parsing).
Variables (R R' : bvmap 5 word).
Variable k : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma cs_of_preserved : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros RP Hk. apply RP. unfold callee_saved_idx. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.
End S.
Lemma regs_preserved_trans : ltac2:(TCodec.tc2 tcn__PmStep "A&Q7y5'SHyR0%211%5241&QMr3r2%3221r5%5214p031p041pS:91pS8:1pS6;1").
Proof. intros R1 R2 R3. intros H1 H2 x Hx. rewrite (H2 x Hx). apply H1. exact Hx. Qed.
Ltac rk :=
first [ reflexivity | greg
| match goal with K : forall x, In x _ -> getr ?Rb (reg x) = getr ?Ra (reg x) |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
constr_eq Rb Rb'; rewrite (K k) by inl; rk end
| match goal with RP : regs_preserved ?Ra ?Rb |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
constr_eq Rb Rb'; rewrite (cs_of_preserved Ra Rb k RP) by inl; rk end ].
Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | alia] ].
Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Ltac pvz_lin P := lazymatch type of P with ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T) in P) | _ => idtac end.
Ltac pvz_clrT := repeat match goal with T := (_ /\ _) : Prop |- _ => clear T end.
Lemma land_m2_even : ltac2:(TCodec.tc2 tcn__PmStep "C'E&RGzr1%3221'A&RIr2+2%3221%53:18&RFr3-2%3221%:3?13p061p0=1pVNB1").
Proof. intros r.
intros Hr He. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by lia.
destruct (Z.eq_dec i 0) as [->|NZ].
- rewrite Z.bit0_eqb. change (Z.testbit 1 0) with true. cbn [negb]. rewrite Bool.andb_false_r. symmetry. apply Z.eqb_neq. lia.
- replace (Z.testbit 1 i) with false. rewrite Bool.andb_true_r. reflexivity. symmetry. rewrite <- (Z.pow_0_r 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma ret_to : ltac2:(TCodec.tc2 tcn__PmStep "S<'8'L%211'R;&Q7y5'SHyR0%211%5241';y8%611%311p061'EyQ0%;11'A%912&Mr7&SGr3%22A1%5241(2r2%22;1%;3:41'4&N%119(6%@3421'='Q6%221F%L11&Q4r4%211(<(Q5(SFz(?%33Q:21+1%53Q<13y<%73165%93531+4%<4BQ721%M2B1%Q63B?1&R<r8&RJu1%211%Q82QI1%6251%Q:2QIH%Q?3QI21'@&RGr5%22H1&RH&RK+2+Q?%3221%5271%:271&RIr6%2217%QN3R11Q3'QEr=&R=r<r;r9%R12R@1r:&R>%118%8576431%R62RER7%:598153%=3<31p0?1p0D1p0Q01p0Q:1p0R11p0R71pVNRF1pUNRE1pVJRH1pRBRJ1pS2S01pV<S71pW6S91").
Proof. intros segs fx R M pc W r.
intros HF HEC HD H1 Hr He. eapply mst_step; [reflexivity | | apply mst_refl].
assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
rewrite (step_jalr_x0 segs R _ M (seg_rom segs) _ (reg 1) (0%bv : bv 12) (Z_to_bv 64 r) HF HEC D H1).
f_equal. f_equal. unfold v_jalr. f_equal. unfold jalr_tgtZ. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r.
rewrite L5.unsigned_lit by lia. apply land_m2_even; lia.
Qed.
Section Kit.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable L : heap_layout.
Variable HI : heap_iface.
Record klayout : Prop := KLAY {
kl_segs : hl_segs L = segs;
kl_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
kl_img : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000;
kl_errno : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L
}.
Hypothesis KL : klayout.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).
Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) model.
Definition cwr (LB : list (Z * Z)) (a : Z) : Prop :=
(hl_ceil L <= a < hl_sptop L) \/ in_block LB a \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ hl_alloc_ro L a).
Lemma hi_heap_stretch : ltac2:(TCodec.tc2 tcn__PmStep "R4'8'='E%2211%411&QG'SHyR0%211';y8%511%311p051pWD62'Q0&QIvFr5r4r3r1%6554321&RG+SoonPPPPP0&QJvH%211%5241'@z%821:&RH&RK+2+R0%3221%52@1%9271'C'Ar6&SGr2%22Q51%411r7%113%83Q431&R6r9%2218%=241p0?1pV6QD1&RA%12?Q6r8%Q:5Q981AQ8p031p061p0Q11p0Q81pULQ@1pRDQB1pRBQD1pV:QM1pQDQO1").
Proof. intros LB cr M M' VM.
intros HH Hsp Hchg Hgr. eapply (hio_frame L SCFG HI HIok). exact HH.
- intros a Ha Hpriv. destruct (Hchg a Ha) as [E|[S|[B|(I1 & I2 & I3)]]]. exact E.
+ exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. lia. apply (kl_ro KL) in P. pose proof (kl_img KL). lia.
+ exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. exact (P2 B). apply (kl_ro KL) in P.
destruct B as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) b Hb) as ((R0 & R1 & R2 & R3 & R4) & _).
pose proof (kl_img KL). lia.
+ exfalso. destruct Hpriv as [(P1 & P2 & P3)|P]. apply P3. split; assumption. exact (I3 P).
- intros x Hx. apply Hgr. exact Hx.
Qed.
Lemma spiece : ltac2:(TCodec.tc2 tcn__PmStep "T@'8'='E%2211%411&QG'SHyR0%211';y8%511%311p051'O'R;&Q7y5%221:!p0B1&R?&QIvFr=r<r;&Q3r:%211%8576541'A%G1H&Q1%118(1%11L%63531%Q52NN%Q711&Q2%11@(:%115%=3531&RG+SoonPPPPP0&QJvH%211%5241'QEvSB&R=&SG%12Q@Kr?&R>%116%65Q3Q1431r9r8%82QG1r7%;5Q74216%>3=61&RAr@%2217'@zr1%K221&RH&RK+2+R0%3221%5271%:271&Br2%QF11%311r3%O2R>1%QM11rD%113%QJ3R=31p071p0<1pV6RJ1%R11F&R6rF%221?p041pV6S01'D%R:1M%E11%3221pV6S51rErC%R?11%RE5RD<3RB1'R@&R4vRB%211&R5rBr>%352QK1RKL%84R051RJp0:1rA%75>1QD?Q0%<4R491RNp041p0C1p0I1p0Q01p0QI1p0QM1p0R=1p0RD1p0RL1p0S41pQ@S>1pUNS@1pRHSH1pVLT41pS6SE1pVJT61pS2SG1pV>SK1pV<SL1pVFSN1pRBT01pV:T91pQDT;1").
Proof. intros LB cr M model fx fx1 R pc R1 pc1 M1 W K.
intros HH Hh Hl Hsp MS MG FR WC DEC KONT. unfold cfg.
eapply (L5.cps_of_msteps segs); [exact Hh| exact Hl| exact MS|].
apply KONT. apply (hi_heap_stretch LB cr M M1 _ HH Hsp); [|exact MG].
intros a Ha. destruct (DEC a) as [Y|N]; [right; apply WC; exact Y| left; apply FR; assumption].
Qed.
Lemma spiece_ro : ltac2:(TCodec.tc2 tcn__PmStep "R9'O'R;&Q7y5'SHyR0%211%5241'E';y8%711%311p071&R?'A%71:&Q1r9%211(1%11?%73631'8'=%12CC%311&Q2r:%211(:%116%A3631'QEvSB&R=r8&SGr7%22Q21r4&R>%118%85?7431r6r5%92Q91%<5M3175%?3>51'R@&R4vRB%211&R5r<%25KA;:1%74F41@r=%554NQ8>1%:4I71>p041p0=1p0N1p0Q91pQ@QB1pRBQD1pVLQJ1pS6QL1pVJQL1pS2QN1pV>R51pV<R61pVFR81").
Proof. intros model fx fx1 R pc R1 pc1 M K. intros Hh Hl MS KONT. unfold cfg in *. eapply (L5.cps_of_msteps segs); eauto. Qed.
Lemma rng_dec : ltac2:(TCodec.tc2 tcn__PmStep "A'E'D'@&RGr2r3%3221&RHr1%2241%8241&B%112%<231pV@>1pVD?1pV6@1").
Proof. intros a lo hi. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia]. Qed.
Lemma or_dec : ltac2:(TCodec.tc2 tcn__PmStep "@!'Dr2&B%112%4231'Cr4r3%3221%711%:221p071p081pS0>1pRN?1").
Proof. intros P Q. intros [p|np] [q|nq]; [left; auto| left; auto| left; auto| right; tauto]. Qed.
Lemma cwr_stack : ltac2:(TCodec.tc2 tcn__PmStep "Q7'8'='E%2211%411'SHyR0%211';y8%511%311p051&R0&QJvH%211r4r3r2%744321'@&RG&RL%1276%3216&RH%128;%7231&R6r7%221=p041p0=1pV6Q01pW0Q11pW8Q21pRBI1pQDQ21").
Proof. intros LB M sp scr a. intros (_ & B & _ & _ & _) Ha. left. lia. Qed.
Lemma cwr_block : ltac2:(TCodec.tc2 tcn__PmStep "M'8'='E%2211%411&RC(<r3r2%347721r4%63821'@&RG%1246&RH&RE%127:%32:1%7251&R6r6%221?p041p0=1pV6G1pVHH1p2I1pQDH1").
Proof. intros LB B n a. intros Hin Ha. right. left. exists (B, n). split; [exact Hin| cbn; lia]. Qed.
Definition inW (W : list L5.range) (a : Z) : Prop := exists r, In r W /\ L5.in_rng r a.
Lemma inW_not_outside : ltac2:(TCodec.tc2 tcn__PmStep "@'8&R3%211'E&R9r2r1%3221&B&R2r3%2216%411p061pV6;1pUN=1").
Proof. intros W a. intros (r & Hin & Hr) HO. exact (HO r Hin Hr). Qed.
Lemma inW_here : ltac2:(TCodec.tc2 tcn__PmStep "M'E'8'=%1233%311'@&RGr4r1%3221&RH&REr3%2261%4261%:261&R9(5(<r5%24DD1=%43B19r2%7221p091pV6I1pUNF1pVHK1pV8L1").
Proof. intros b n W a. intros H. exists (b, n). split; [left; reflexivity| exact H]. Qed.
Lemma inW_next : ltac2:(TCodec.tc2 tcn__PmStep "A&R3'8%112'E&R9r2r1%3221(5r4r3%33;21%8217p061pV6;1pUN=1pVN@1").
Proof. intros r W a. intros (r' & Hin & Hr). exists r'. split; [right; exact Hin| exact Hr]. Qed.
Lemma inW_app_l : ltac2:(TCodec.tc2 tcn__PmStep "A'8&R3%211'E&R9r3r1%3221&3r4%23915r2%8221p061pV6;1pV4=1pV2>1").
Proof. intros W1 W2 a. intros (r & Hin & Hr). exists r. split; [apply in_or_app; left; exact Hin| exact Hr]. Qed.
Lemma inW_app_r : ltac2:(TCodec.tc2 tcn__PmStep "A'8&R3%211'E&R9r2r1%3221&3r4r3%33:21%8217p061pV6;1pV4=1pV2>1").
Proof. intros W1 W2 a. intros (r & Hin & Hr). exists r. split; [apply in_or_app; right; exact Hin| exact Hr]. Qed.
Definition ek (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
forall a, L5C.kept L LB sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition dk (LB : list (Z * Z)) (sp scr : Z) (M M' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp scr a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
Lemma hpres_of : ltac2:(TCodec.tc2 tcn__PmStep "Q<'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&R8r6r5r4r3r2r1%76654321&R1&RL%1298%33619&R7r8r7%3521><;&QOvHr9%372165BA@p051p0:1p0?1pRDH1pRBI1pUNQ21pW0Q71pW8Q81pQDQ71").
Proof. intros LB sp scr W M M'. intros E D K. apply L5C.hpres_intro; assumption. Qed.
Lemma ek_of_hpres : ltac2:(TCodec.tc2 tcn__PmStep "Q2'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QOvHr6r5r4r3r2r1%877654321&R8r7%26198765p041pRD>1pRB?1pUNH1pW0M1pW8N1pQDM1").
Proof. intros LB sp scr W M M'. intros H a Ha. apply (L5C.hpres_kept L LB sp scr W M M' a H Ha). Qed.
Lemma dk_of_hpres : ltac2:(TCodec.tc2 tcn__PmStep "Q2'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QOvHr6r5r4r3r2r1%877654321&R7r7%2519865p041pRD>1pRB?1pUNH1pW0M1pW8N1pQDM1").
Proof. intros LB sp scr W M M'. intros H a Ha C E D. apply (L5C.hpres_cdef L LB sp scr W M M' a H Ha C E D). Qed.
Lemma ek_refl : ltac2:(TCodec.tc2 tcn__PmStep "K'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&R8r5r4r3r2r1%66543211pRB81pUNA1pW0F1pW8G1pQDF1").
Proof. intros LB sp scr W M. intros a _. reflexivity. Qed.
Lemma ek_trans : ltac2:(TCodec.tc2 tcn__PmStep "Q4'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&R8r7r6r5r4r3r2%76654321r8%96187643r9%;613:986p031p061pRL?1pRJ@1pRHA1pUNJ1pW0O1pW8Q01pQDO1").
Proof. intros LB sp scr W M1 M2 M3. intros H1 H2 a Ha. rewrite (H2 a Ha). apply H1. exact Ha. Qed.
Lemma dk_refl : ltac2:(TCodec.tc2 tcn__PmStep "G'8'='E%2211%411'SHyR0%211';y8%511%311p051&R7r4r3r2r1%5543211pRB71pW0B1pW8C1pQDB1").
Proof. intros LB sp scr M. intros a _ _ _ D. exact D. Qed.
Lemma dk_trans : ltac2:(TCodec.tc2 tcn__PmStep "Q0'8'='E%2211%411'SHyR0%211';y8%511%311p051&R7r6r5r4r3r2%6554321r7%8517643r8%:513986p031p061pRL>1pRJ?1pRH@1pW0K1pW8L1pQDK1").
Proof. intros LB sp scr M1 M2 M3. intros H1 H2 a Ha C E D. apply (H2 a Ha C E). apply (H1 a Ha C E D). Qed.
Lemma dk_grows : ltac2:(TCodec.tc2 tcn__PmStep "M'8'='E%2211%411'SHyR0%211';y8%511%311p051&RAr2r1%3221&R7r6r5r4r3%5543218p071pRD<1pRB=1pW0H1pW8I1pQDH1").
Proof. intros LB sp scr M M'. intros G a _ _ _ D. apply G. exact D. Qed.
Lemma client_mono : ltac2:(TCodec.tc2 tcn__PmStep "Q;'8'='E%2211%411&QFvHr7r5r4r1%6554321&RDr8%23;17'@&RG&RLr6%221;%421:&RH%12<4%8231r9%821<r2%;221%7224%>221p071pWDM1%K5J8>HGp021p0D1p0H1pV6Q21pW2Q31pW:Q41pW0Q51pW8Q61pQHQ51pQDQ61").
Proof. intros LB LBc sp scr sp' scr' a.
intros [(b & Hb & Hr)|[[S1 S2]|IM]] Hi Hs.
- left. exists b. split; [apply Hi; exact Hb| exact Hr].
- right. left. split; [exact S1|]. intros X. apply S2. apply Hs. exact X.
- right. right. exact IM.
Qed.
Lemma client_narrow : ltac2:(TCodec.tc2 tcn__PmStep "Q2'8'='E%2211%411&QFvHr6r5r4r1%6554321&B'@&RG&RLr3%2281r2%5221&RH%123<%9231%;11r8%D5C1A@9p031p0@1pV6J1pW2K1pW:L1pW0M1pW8N1pQDM1").
Proof. intros LB sp scr sp' scr' a. intros [B|[[S1 S2]|IM]] O; [left; exact B| right; left; split; assumption| right; right; exact IM]. Qed.
Lemma ek_piece : ltac2:(TCodec.tc2 tcn__PmStep "R<'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311pWD51!p0>1'@&RGzr1%3221&RH&RK+2+R0%3221%5271%;271&Br3r2%211%411'Ar5&SG%12M7%311r6%113%73L31p091p0?1pV6Q:1&QFvHr:r9r8%554321C&QL%126F%H11&R2r4%2281r7%11G%N11p041p081p0<1p0Q31pV6QN1&R8%16BA9KO;p031p0H1pRNQE1pRDQH1pRBQI1pUNR21pW0R71pW8R81pQDR71").
Proof. intros LB sp scr W M M' P. intros E X a (Ha & Hc & He & Ho). apply E; [exact Ha|]. apply X; assumption. Qed.
Lemma ek_piece_in : ltac2:(TCodec.tc2 tcn__PmStep "RN'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311pWD51!p0>1'@&RGzr1%3221&RH&RK+2+R0%3221%5271%;271&Br3r2%211%411'Ar5&SG%12M7%311r6%113%73L31p091p0?1pV6Q:1&R0&QJvH%211r4r7%64321<&RCr:%23QCQ21&RE&7%13QGQGJ&>%13QIQIL%5231&RL+XPPP0%22?1%Q>241p0;1pV8QO1%Q01Q?'Cr;%921A%QE21Q8%QB2Q93%QH221&R9r9%221Q=%9241p0;1pV6R=1&R8r8%26=M71Q0Q;p041p0B1p0Q21p0Q:1pRNR71pRDR:1pRBR;1pUNRD1pW0RI1pW8RJ1pQDRI1").
Proof. intros LB sp scr W M M' P.
intros E (_ & Hc & _ & Hw & _) HLB FP. apply (ek_piece LB sp scr W M M' P E). intros a Ha CA NE OW Pa.
destruct (FP a Pa) as [S|I]; [|exact (inW_not_outside W a I OW)].
destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
- pose proof (HLB b Hb). lia.
- exact (S2 S).
- pose proof (kl_img KL). lia.
Qed.
Lemma ek_piece_in' : ltac2:(TCodec.tc2 tcn__PmStep "S1'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311pWD51!p0>1'@&RGzr1%3221&RH&RK+2+R0%3221%5271%;271&Br3r2%211%411'Ar5&SG%12M7%311r6%113%73L31p091p0?1pV6Q:1&RL&QJvH%211+XPPP0%5221r7%721=%Q3231+SoonPPPPP0%Q5217&RCr;%23QGQ61&RE&7%13QKQKN&>%13QMQMQ0%5231%Q?21?p081pV8R01%M1Q@'Cr<%J21>%QF21Q9%QC2Q:3%QI221&R9r:%221Q>%9241p0;1pV6R>1&R8r9r8%36>K821Q1p051p0C1p0Q01p0Q31p0Q=1pRNR:1pRDR=1pRBR>1pUNRG1pW0RL1pW8RM1pQDRL1").
Proof. intros LB sp scr W M M' P.
intros E Hc Hw HLB FP. apply (ek_piece LB sp scr W M M' P E). intros a Ha CA NE OW Pa.
destruct (FP a Pa) as [S|I]; [|exact (inW_not_outside W a I OW)].
destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]].
- pose proof (HLB b Hb). lia.
- exact (S2 S).
- pose proof (kl_img KL). lia.
Qed.
Lemma ek_heap : ltac2:(TCodec.tc2 tcn__PmStep "QD'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QHvHr7r4r2r1%6554321&RDr9r8%33F21&RG&RL%124;r6&QK%11?%5231%7251%82A;&R8r<r:r5%4632@F:1p061p081p0A1p0F1pRDN1pRBO1pUNQ81pW:Q=1pW0Q>1pW8Q?1pQHQ>1pQDQ?1").
Proof. intros LB LBc sp scr sp' W M M'.
intros [P _] Hi H1 H2 a (Ha & Hc & He & _). apply P; [exact Ha| |exact He].
apply (client_mono LB LBc sp scr sp' (hl_stack L) a Hc Hi). intros x Hx. lia.
Qed.
Lemma dk_heap : ltac2:(TCodec.tc2 tcn__PmStep "Q@'8'='E%2211%411'SHyR0%211';y8%511%311p051&QHvHr6r3r2r1%6554321&RDr8r7%33D21&RG&RL%124;r5&QK%11?%5231%7251%82A;&R7r;r9%3521?E9p051p071p0@1p0E1pRDM1pRBN1pW:Q91pW0Q:1pW8Q;1pQHQ:1pQDQ;1").
Proof. intros LB LBc sp scr sp' M M'.
intros [P D] Hi H1 H2 a Ha Hc He HM. destruct (rng_dec a (sp' - hl_stack L) sp') as [I|O]; [apply D; exact I|].
rewrite P; [exact HM| exact Ha| | exact He]. apply (client_narrow LBc sp scr sp' (hl_stack L) a); [|exact O].
apply (client_mono LB LBc sp scr sp scr a Hc Hi). intros x Hx. exact Hx.
Qed.
Lemma ek_callee : ltac2:(TCodec.tc2 tcn__PmStep "R0'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QOvHr9r6r5r3r2r1%877654321&RDr;r:%33H21&RG&RL%124=r8r7%4221%6241%72B:&QFr?r=r<%45H321B&R2%12@E%22AGp021p051pV6Q<1&R8%16;:9O@Np031p0?1p0A1p0I1p0N1pRDQ81pRBQ91pV0QB1pUNQC1pW2QH1pW:QI1pW0QJ1pW8QK1pQHQJ1pQDQK1").
Proof. intros LB LBc sp scr sp' scr' W W' M M'.
intros HP Hi H1 H2 HW a (Ha & Hc & He & Ho). apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
split; [exact Ha|]. split; [|split; [exact He| apply HW; assumption]].
apply (client_mono LB LBc sp scr sp' scr' a Hc Hi). intros x Hx. lia.
Qed.
Lemma dk_callee : ltac2:(TCodec.tc2 tcn__PmStep "QE'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QOvHr8r5r4r3r2r1%877654321&RDr:r9%33H21&RG&RL%124=r7r6%4221%6241%72B:&R7r=r;%3521>7Ep051p071p0?1p0D1pRDN1pRBO1pV0Q81pW2Q=1pW:Q>1pW0Q?1pW8Q@1pQHQ?1pQDQ@1").
Proof. intros LB LBc sp scr sp' scr' W' M M'.
intros HP Hi H1 H2 a Ha Hc He HM. destruct (rng_dec a (sp' - scr') sp') as [I|O].
- pose proof (L5C.hpres_defined L LBc sp' scr' W' M M' HP) as D. replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply D. lia.
- apply (L5C.hpres_cdef L LBc sp' scr' W' M M' a HP Ha); [|exact He| exact HM].
apply (client_narrow LBc sp scr sp' scr' a); [|exact O]. apply (client_mono LB LBc sp scr sp scr a Hc Hi). intros x Hx. exact Hx.
Qed.
Lemma ek_callee_in : ltac2:(TCodec.tc2 tcn__PmStep "RK'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QOvHr:r7r6r4r2r1%877654321&RDr<r;%33H21&RG&RL%124=r9r8%4221%6241%72B:&R0&QJ%11Fr=%442F1?&RCrA%23Q8E1&RE&7%13Q<Q<I&>%13Q>Q>K%5231+XPPP0%F2=1%H231p0:1pV8QC1&R9%12NQ2'C'@r@%O2B1%Q121Q8&RH%12Q:E%6231%:2JQ<%9221p0;1pV6R21&R8rBr?%362=1Q?Q9Q8p051p0D1p0Q31p0Q91p0Q;1p0QC1p0QH1pRDR21pRBR31pRFR41pV0R=1pUNR>1pW2RC1pW:RD1pW0RE1pW8RF1pQHRE1pQDRF1").
Proof. intros LB LBc sp scr sp' scr' W W' M0 M M'.
intros HP Hi H1 H2 (_ & Hc & _ & Hw & _) HLB FP. apply (ek_callee LB LBc sp scr sp' scr' W W' M M' HP Hi H1 H2).
intros a CA OW r Hr Hin. destruct (FP a (ex_intro _ r (conj Hr Hin))) as [S|I]; [|exact (inW_not_outside W a I OW)].
destruct CA as [(b & Hb & Hrb)|[[S1 S2]|[IM _]]].
- pose proof (HLB b Hb). lia.
- exact (S2 S).
- pose proof (kl_img KL). lia.
Qed.
Lemma ek_callee_in' : ltac2:(TCodec.tc2 tcn__PmStep "RN'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&QOvHr9r6r5r3r2r1%877654321&RDr;r:%33H21&RG&RL%124=r8r7%4221%6241%72B:&QJ%11E+XPPP0%:221r<%<21@%>231+SoonPPPPP0%@217&RCrA%23Q<I1&RE&7%13Q@Q@M&>%13QBQBO%5231%J21?p081pV8QE1&R9%12Q1Q4'C'@r@%Q12@1%Q321Q:&RH%12Q<C%6231r=%;21Q?%:231p0<1pV6R51&R8rBr?%362>1Q3QAQJp051p0E1p0Q21p0Q51p0Q=1p0Q?1p0QG1p0QL1pRDR61pRBR71pV0R@1pUNRA1pW2RF1pW:RG1pW0RH1pW8RI1pQHRH1pQDRI1").
Proof. intros LB LBc sp scr sp' scr' W W' M M'.
intros HP Hi H1 H2 Hc Hw HLB FP. apply (ek_callee LB LBc sp scr sp' scr' W W' M M' HP Hi H1 H2).
intros a CA OW r Hr Hin. destruct (FP a (ex_intro _ r (conj Hr Hin))) as [S|I]; [|exact (inW_not_outside W a I OW)].
destruct CA as [(b & Hb & Hrb)|[[S1 S2]|[IM _]]].
- pose proof (HLB b Hb). lia.
- exact (S2 S).
- pose proof (kl_img KL). lia.
Qed.
Lemma ek_weaken : ltac2:(TCodec.tc2 tcn__PmStep "R0'8'='E%2211%411&R3%611'SHyR0%211';y8%511%311p051&R8r9r6r5r3r2r1%76654321&RDr;r:%33G21'@&RG&RLr8%22?1%421;&RH%12=B%8231r<%821=%:21B%62C3%=221p061pWDQ81&R2%12>G%22?Ip021pV6Q=1r>%Q261=ICQ0Op031p091p0J1p0O1pRDQ81pRBQ91pV4QB1pUNQC1pW4QH1pW<QI1pW0QJ1pW8QK1pQFQJ1pQDQK1").
Proof. intros LB LB2 sp scr sp2 scr2 W W2 M M'.
intros E Hi Hs HW a (Ha & Hc & He & Ho). apply E. split; [exact Ha|]. split; [|split; [exact He| apply HW; exact Ho]].
apply (client_mono LB LB2 sp scr sp2 scr2 a Hc Hi Hs).
Qed.
Lemma stk_call : ltac2:(TCodec.tc2 tcn__PmStep "Q<'SHyR0%211';y8%511%311p051'E&R0&QJvH%211r5r4r3%744321&RG%1235&RLr6%2218%3287%6221z%821;'A&RI+@%2291%43F16r:r7%H4E21=p041p0:1p0=1p0C1p0F1pW2O1pW:Q01pW0Q11pW8Q21pRBQ41").
Proof. intros M sp scr sp' scr'.
intros (A16 & B & C & D & W) H1 H2 H3 H4. split; [exact H4|]. split; [lia|]. split; [lia|]. split; [exact D|].
apply (L5.defined_sub M (sp - scr) scr); [exact W| lia| lia].
Qed.
Lemma stk_after : ltac2:(TCodec.tc2 tcn__PmStep "QF'8'='E%2211%411'SHyR0%211';y8%511%311p051&R3%>11&R0&QJvH%211r7r5r4%744321&QOr9r3r2r8%57;473219&RG%12:;&RL%125=r6%321>%6231z%8214r;r:%I4F21@p041p071p0=1p0@1p0G1pV0Q01pW2Q=1pW:Q>1pW0Q?1pW8Q@1pRDQ71pRBQ81pQHQA1").
Proof. intros LBc M M' sp scr sp' scr' W'.
intros (A16 & B & C & D & W) HP H1 H2 H3. split; [exact A16|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
intros i Hi. set (a := sp - scr + i). destruct (rng_dec a (sp' - scr') sp') as [I|O].
- pose proof (L5C.hpres_defined L LBc sp' scr' W' M M' HP) as DD. replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply DD. lia.
- pose proof (kl_img KL) as KI. pose proof (kl_errno KL) as KE.
apply (L5C.hpres_cdef L LBc sp' scr' W' M M' a HP); [unfold a; lia| | unfold in_errno, a; lia| apply W; exact Hi].
right. left. split; [unfold a; lia| exact O].
Qed.
Lemma stk_after_heap : ltac2:(TCodec.tc2 tcn__PmStep "QB'8'='E%2211%411'SHyR0%211';y8%511%311p051&R0&QJvH%211r5r3r2%744321&QHr7r6%3592517&RG%1289&RL%125;r4&QK%11@%5231%8251z%:214r9r8%I4F21@p041p071p0?1p0B1p0G1pW:Q:1pW0Q;1pW8Q<1pRDQ31pRBQ41pQHQ=1").
Proof. intros LBc M M' sp scr sp'.
intros (A16 & B & C & D & W) [P DD] H1 H2 H3. split; [exact A16|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
intros i Hi. set (a := sp - scr + i). destruct (rng_dec a (sp' - hl_stack L) sp') as [I|O].
- apply DD. exact I.
- pose proof (kl_img KL) as KI. pose proof (kl_errno KL) as KE.
rewrite P; [apply W; exact Hi| unfold a; lia| | unfold in_errno, a; lia]. right. left. split; [unfold a; lia| exact O].
Qed.
Lemma stk_grows : ltac2:(TCodec.tc2 tcn__PmStep "K'SHyR0%211';y8%511%311p051'E&RAr4r3%3221&R0&QJvH%211r5r2%643281%7443:9p021p0:1pW0?1pW8@1pRDB1pRBC1").
Proof. intros M M' sp scr. apply L5C.stk_grows. Qed.
Lemma stack_ok_of_stk : ltac2:(TCodec.tc2 tcn__PmStep "Q>'SHyR0%211';y8%511%311p051'E&R0&QJvH%211r4r3r2%744321&RG%1235&RLr5%2218&QK%11<%52:1%8241z%:214'A&RI+@%22;1%43H16&QNr9r6%33I21p051p0;1p0>1p0F1p0I1pW:Q21pW0Q31pW8Q41pRBQ61").
Proof. intros M sp scr sp'.
intros (A16 & B & C & D & W) H1 H2 H3 H4. unfold stack_ok. split; [exact H4|]. split; [lia|]. split; [lia|]. split; [exact D|].
intros d m Hd Hm. rewrite (kl_segs KL).
apply (L5C.writable_of_defined segs M (sp' - hl_stack L) (hl_stack L)); [|lia|lia|exact Hd|exact Hm].
apply (L5.defined_sub M (sp - scr) scr); [exact W| lia| lia].
Qed.
End Kit.
End PMK.
