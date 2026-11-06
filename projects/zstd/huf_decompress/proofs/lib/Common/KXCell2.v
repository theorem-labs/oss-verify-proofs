(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXCell.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KXCell2 () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedK69OSSVerify5KrLib6Common6KXExec3KX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS5elenZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I69OSSVerify5KrLib6Common6KXExec3KX23env00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib6Common7KXSound3KXS7know_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib6Common6KXExec3KX26sentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib6Common7KXSound3KXS8log_flatC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost:kx_apart_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXCell<log_flat_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem9log_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost;kx_apart_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib6Common7KXCell2<kx_elenZ_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXCell>kx_cell_store8C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX25saddr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX24expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXCell>kx_cell_store4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX22evC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00".
Import ListNotations.
Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Cell2.
Variable segs : list Segment.

Lemma kx_elenZ_lit : forall E k, 0 <= k < 2^64 -> elenZ E (ELit k) = k.
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell2 ()) ["Cell2"] "h04__x1h11Eh22Hkh37__arithh44__ffh58__varmaph65__with71kh81zp;2p;1p;3p;4p;7p;8p;6g0000j2<Tg000Lj10Tg0011j19Tg001Oj28Tg001lj23Tg002Hj21Tg002cj1MTg003Aj2DTg003gj32Tg004Aj27Tg004[j1@Tg005;j1>Tg005[j2=Tg0069j1UTg006Wj1TTg007Bj2;Tg007ej2STg008Hj4:Tg0093j3LTg009Vj7KTg00::j1JTg00:\j8CTg00;@j2ETg00;bj2FTg00<Nj3BTg00<mj4GTg00=_j1HTg00>=j1ATg00>fj3ITg00?Rj65Tg00@0j2?Tg00@Vj24Tg00A@j2NTg00Aoj1OTg00Blj2PTg00Cij2QTg00Dfj7RTf1R0g00EJR1g00EiR2P2g00FIR3f0R4g00FiFRp=6g00GIg00HER5g00HcR6/<4g00IAR7#0R8#9R9%08#0#0#0#0R8#9'8R:,34'1R;P5%M8R8/D0R<f2R=9254X85R>P5P0P>1750P<g00IfR<#@%><1=50%U5%T5R<P1P2P2P3P<P1P2P2P3P51;56g00JR1S57R7C:,6<P5P7g00K91;59=L58C:,6<FKR7%J2P7GC1E<3P4P=g00K`R<g00L@R3'71F4==2<3dAB560CGb4b5b6X051<60R6130:'1\;^05P4P=P0O2b3%H8,89,30,16e%A8,30,16e9I80E51?80,481N80E5%O0R6,P=,48=250e1Q=6=250eW2W7W1o"). Qed.

Lemma kx_cell_store8c : forall E m kn pre a v rest A w0,
  know_ok segs E m kn -> log_flat E (pre ++ SE a 8 v :: rest) -> rw_cells segs m A [C8 w0] ->
  estart E a = A -> kx_apart_b kn pre a (ELit 8) = true ->
  rw_cells segs (mem_denot E m (pre ++ SE a 8 v :: rest)) A [C8 (edenot E v)].
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell2 ()) ["Cell2"] "h01Dh11zh21Ah31Eh42HKh52Hah62Hbh72Hch82Hfh93Hfph:2_Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@2a0hA2knhB1mhC3prehD4resthE1vhF2w0p;1p;4p;3p;2p;:p;6p;7p;=g000Lj12Tg002cj1BTg00L`j1>Tg00MCj1FTg005;j1;Tg00Mej4VTg00Ndj10Tg00OCj35Tg00PBj34Tg00Pbj3GTg00Q?j21Tg00R?j1DTg004[j1@Tg00S4j4[Tg00Sjj28Tg003gj3:Tg0011j19Tg00Aoj1UTg00Thj4TTg00Uej4LTg002HR0j2?Tg00Vdj43Tg00W_l:KTg00Cij26Tg00X]j6=Tg00Y9j1JTg0069j1ITg006Wj1HTg007Bj27Tg008Hj4ATg0093j3ETg009Vj7MTg00;@j2NTg004Aj2OTg00;bj2PTg00<Nj3QTg00<mj4CTg0000j2RTg001Oj2STg001lj2ZTg00YWj3YTg00ZWl=XTg00Dfj7WTf1R1g00EJR2g00EiR3P3g00FIR4f0R5g00FiFWp=<g00GIg00IA#2R6#2#2R7#2#2#2R8#BR9#>R:%B7#>#F[g00[X#;g00\WR;#;R<g00]Vg00^Tg00HER=p,4segsR>f8R?f7R@f6RACVf9RBf5RCg00_Q#0#0#0#0#0#0#0#0RDf4RE35f3RF54;9G;A'1P>PBPFg00`0RGf2RH#D%@G34C[f;RG/8@=:=Eg00K`REf:RIPBP?%97R7#URJCTg00L@RK3:P>f=RLf<RMPIPBP?P@PAPCPFPHP1PLPIA5BD?=4;@RAPFCL11LI11LA'?P0f>R0/1GA5IDB=4;?,10f?RIPMP?P7C3P5f@R?/1LfARAA5LDM=4;G'1P>fBR>PAP?PIP0PJPBP1PCM:KP>PI18>016>JC3P=fCRC/8IfDRIPAP516IJRBC3X1=P5PMP@E=PCP?PM16CJC3P=PBfEP>P0P5C3X1=P5P7g00IfR0#@%;0%J=%I=%H=R0P2P3P3P4P=g00HcR3,7=g00JR17=7R2CA,<0P=P2g00K9%96R6,7==E=9CA,<0FM1N04P5PH1OEK1P5H=:EKdAQ=31CCb<b=b>1R37%98,S6,Z7'?P5b;9YI7E=PIPAPLP7C3P5b0b0b0W:W9P1P5O2n2001000000121000000b@M=XW6W5W7W8W4XF:W2XD<WEW?WCWAWBW3o"). Qed.

Lemma kx_cell_store4c : forall E m kn pre a v rest A w0,
  know_ok segs E m kn -> log_flat E (pre ++ SE a 4 v :: rest) -> rw_cells segs m A [C4 w0] ->
  estart E a = A -> kx_apart_b kn pre a (ELit 4) = true ->
  rw_cells segs (mem_denot E m (pre ++ SE a 4 v :: rest)) A [C4 (edenot E v)].
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell2 ()) ["Cell2"] "h01Dh11zh21Ah31Eh42HKh52Hah62Hbh72Hch82Hfh93Hfph:2_Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@2a0hA2knhB1mhC3prehD4resthE1vhF2w0p;1p;4p;3p;2p;:p;6p;7p;=g000Lj11Tg002cj1BTg00L`j1>Tg00MCj1FTg005;j1;Tg00Mej4VTg00Ndj14Tg00OCj35Tg00PBj33Tg00Pbj3GTg00Q?j20Tg00`ej1DTg004[j1@Tg00S4j4[Tg00Sjj28Tg003gj3:Tg0011j19Tg00Aoj1UTg00Thj4TTg00Uej4LTg002HR0j2?Tg00Vdj42Tg00W_l:KTg00Cij26Tg00X]j6=Tg00Y9j1JTg0069j1ITg006Wj1HTg007Bj27Tg008Hj4ATg0093j3ETg009Vj7MTg00;@j2NTg004Aj2OTg00;bj2PTg00<Nj3QTg00<mj4CTg0000j2RTg001Oj2STg001lj2ZTg00YWj3YTg00aZl=XTg00Dfj7WTf1R1g00EJR2g00EiR3P3g00FIR4f0R5g00FiFWp=<g00GIg00IA#1R6#1R7#1R8#1#1#1R9#BR:#>R;%B8#>#F[g00[X#;g00\WR8#;R<g00]Vg00^Tg00HER=p,4segsR>f8R?f7R@f6RACVf9RBf5RCg00_Q#4#4#4#4RDf4RE35f3RF5389G8A'0P>PBPFg00`0RGf2RH#D%@G33C[f;RG/8@=:=Eg00K`REf:RIPBP?%97R7#URJCTg00L@RK3:P>f=RLf<RMPIPBP?P@PAPCPFPHP1PLPIA5BD?=38@RAPFCL10LI10LA'?P0f>R0/0GA5IDB=38?,00f?RIPMP?P7C2P5f@R?/0LfARAA5LDM=38G'0P>fBR>PAP?PIP0PJPBP1PCM:KP>PI18>016>JC2P=fCRC/8IfDRIPAP516IJRBC2X1=P5PMP@E=PCP?PM16CJC2P=PBfEP>P0P5C2X1=P5P7g00IfR0#@%;0%J=%I=%H=R0P2P3P3P4P=g00HcR3,7=g00JR17=7R2CA,<0P=P2g00K9%96R6,7==E=:CA,<0FM1N04P5PH1OEK1P5H=:EKdAQ=31CCb<b=b>1R37%99,S6,Z7'?P5b;9YI7E=PIPAPLP7C2P5b0b0b0W:W9P1P5O2n2001000000121000000b@M=XW6W5W7W8W4XF;W2XD<WEW?WCWAWBW3o"). Qed.

End Cell2.

Ltac kx_cellc_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m0' ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (first [ eapply (kx_cell_store8c segs E m kn pre a v rest A)
                                    | eapply (kx_cell_store4c segs E m kn pre a v rest A) ];
                              [ exact HK
                              | change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H
                              | change E with (kE zv xs); kx_estart_z zv
                              | vm_compute; reflexivity ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                        cbv [ez] in Hn; change (length zv) with na in Hn; cbv [nth Nat.ltb Nat.leb] in Hn;
                        rewrite ?Z_to_bv_bv_unsigned in Hn;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "kx_cellc: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac kx_cellc H := kx_cellc_gen H 8%nat.
Ltac kx_cell4c H := kx_cellc_gen H 4%nat.

(* [comment removed for export] *)
Lemma kx_edenot_var : forall E j, edenot E (EVar j) = ev E j.
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell2 ()) [] "h01Eh11jp;1p;2g000Lj10Tg002cj14Tg00L`j12Tg00b[j21Tg004Aj23Tg00GIg00cTg00IA#0#0#0#0#0#0#4#2f1f0'1'3W1W0o"). Qed.

Ltac kx_cellw_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m0' ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (first [ eapply (kx_cell_store8c segs E m kn pre a v rest A)
                                    | eapply (kx_cell_store4c segs E m kn pre a v rest A) ];
                              [ exact HK
                              | change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H
                              | change E with (kE zv xs); kx_estart_z zv
                              | vm_compute; reflexivity ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        lazymatch v with EVar ?j => rewrite (kx_edenot_var E j) in Hn | _ => idtac end;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "kx_cellw: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac kx_cellw H := kx_cellw_gen H 8%nat.
Ltac kx_cell4w H := kx_cellw_gen H 4%nat.

(* [comment removed for export] *)
Ltac kx_cellz_gen H W :=
  kx_cellw_gen H W;
  lazymatch goal with
  | KXA : forall j, (j < length ?zv)%nat -> ev ?E j = _ |- _ =>
      revert H;
      lazymatch goal with
      | |- rw_cells _ _ _ [C8 (edenot E ?v)] -> _ => rewrite (ez_ok zv E KXA v)
      | |- rw_cells _ _ _ [C4 (edenot E ?v)] -> _ => rewrite (ez_ok zv E KXA v)
      | |- rw_cells _ _ _ [C8 (ev E ?j)] -> _ => rewrite <- (kx_edenot_var E j); rewrite (ez_ok zv E KXA (EVar j))
      | |- rw_cells _ _ _ [C4 (ev E ?j)] -> _ => rewrite <- (kx_edenot_var E j); rewrite (ez_ok zv E KXA (EVar j))
      end;
      let na := eval vm_compute in (length zv) in
      cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
      kx_norm_m1;
      intro H
  end.
Ltac kx_cellz H := kx_cellz_gen H 8%nat.
Ltac kx_cell4z H := kx_cellz_gen H 4%nat.
