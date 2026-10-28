(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ShadowTac () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z4lxorK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symI47Corelib4Init5Logic2eq00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z9mod_smallC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge<zb_lxor_signC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00".
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  end.

Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

Ltac pr := match goal with |- evtF _ _ _ (MS ?r _ ?pc _ _ ?mm _) => idtac pc; idtac r end.
Ltac prr l := match goal with |- evtF _ _ _ (MS ?r _ ?pc _ _ ?mm _) => idtac "pc=" pc;
  let rec go l := lazymatch l with | nil => idtac | ?k :: ?l' => let v := reg_val k in idtac k "=" v; go l' end in go l end.

(* [comment removed for export] *)
Ltac is_closed_lits E :=
  lazymatch E with
  | Z.add ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.sub ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.of_nat ?k => idtac
  | _ => is_Zlit E
  end.

Ltac addr_eq_tac_fast :=
  lazymatch goal with
  | |- Z_to_bv 64 ?e = wa ?t =>
      tryif (is_closed_lits e; is_closed_lits t)
      then (unfold wa; f_equal; vm_compute; reflexivity)
      else (symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ])
  | _ => symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
  end.

(* [comment removed for export] *)
Ltac acc_facts B := assert (B : True) by exact I.

Ltac solve_acc_shadow H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        Z.div_mod_to_equations; lia
      end
  end.

Ltac acc_hint_shadow :=
  lazymatch goal with
  | |- acc_in _ (Z_to_bv 64 ?E, _) =>
      first [ assumption      (* [comment removed for export] *)
            | is_closed_lits E; match goal with H : rng _ 65536 _ |- _ => solve_acc_with H end
            | lazymatch E with context [Z.shiftr _ 3] =>
                match goal with H : rng _ (shad _) _ |- _ => solve_acc_shadow H end
              end ]
  end.

(* [comment removed for export] *)
Ltac small_offset k :=
  lazymatch k with
  | Z0 => idtac
  | Zpos ?p => let b := eval vm_compute in (Z.ltb k 65536) in lazymatch b with true => idtac end
  end.

Ltac solve_load_guarded :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        small_offset k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        small_offset k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m a n = Some ?bs |- _ =>      (* [comment removed for export] *)
        rewrite HR
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_guarded :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        small_offset k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma aip_zero : forall a s, 0 <= a < 8 -> (s = 0 \/ (0 < s <= 7 /\ a < s)) ->
  Z.land (Z.b2z (0 <? s)) (Z.lxor (Z.b2z (Z.lxor a 9223372036854775808 <? Z.lxor s 9223372036854775808)) 1) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowTac ()) ["CANSEC1"] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with61Hh71zh82Hsh94__p2h:4__x2h;1bh<1mh=1nh>1sh?2Hah@1ap;2p;1p;6p;3p;4p;7p;8g0000j24Tg000Lj12Tg0011j1:Tg001Oj20Tg001kR0j21Tg002Fj1@Tg002kR1j2]Tg003Ej29Tg003cj2UTg004=j6?Tg004[j2RTg0058j2>Tg005Uj2GTg0065j27Tg006Rj1ATg006oj2`Tg007Oj1_Tg007oj1^Tg008Oj2MTg008mj1\Tg009Kj1[Tg00:6j2CTg00:Yj2JTg00;<j1ZTg00;^j2YTg00<@j2XTg00<lj3WTg00=Kj4VTg00>=j4HTg00>Yj3BTg00?3j1gTg00?Qj4fTg00?oj1TTg00@Mj3STg00A0j3KTg00ASj6LTg00Aoj3NTg00BRj2QTg00COj2eTg00Cmj4PTg00DXj7dTg00E<j6cTg00E`j7bTg00FDj8aTf0R2#2#2p=Og00FhR3g00GFR47B2p=Ff1R5/72#Ap=6%22#2#2#2#2#2#2#2p=;f2R61952'e=B34p=8g00GdR7g00HDR87B2p=DP3P5g00HdP2CPp=<P5g00IKR9g00IjR:P:g00JJR;P2g00JjFdp=3P5P9P:P:P;P2Ecp=IP6P9P:P:P;P5P2Fbp=5f3R<P9P:P:P;P6P5P2Gap==P3P5g00KJP2CPp=E1445R9g00L1R=#2R>#OR?#:R@,05'1%F51045RA%@=#@RB#:RC,45'11065RD'1']P1%F61046146C'110<6'1164<f4R1%2?#OR?#2#;#;#;#;#;#;#;#:RE'919<E'6%:=RF38P2%F<P3P41642f6RG/9E192E'6;8FX>31U34REP1P2E?W8P2O1104<14<C'1101<'1P3f5RH%:>RI%@B#@#@RB#:'RRJ'>RK%:?,RIRL'GRM174HRN#ARO19HJRP,62;8FX73P31>1JRQ/GLRR1>GJRS/GL/62=8OFX73P3PK162M=8OFX73P3PQ16S2=8OFX73P71741ROP8P01752#DPD[10521765#D[R017<6#D\D1`52P2n2001000000120000000X<3X=3RDP0^<3^=3R0P2P4PHp-0RTg00LVRU#_RV%^URU1M35RW%\3RX%[3RY1C34RZ1J3=R='<,3YR[1IY<R\55Y1IY1R]55Y%Z:R:P[C=1YY;R;P2P61U781X26#DdAW345CVR^b3b4b5X03X1TW91042R_/15/16PA[^03^1T^9TP2f7RA/0G14GCPGP6O4b2O3b6CHAB78OP7P8%A2RO1>AJR`/7SRa#A;8FX;7P717SKRbP8PDP0P2P`PSPVPUP31M36P5%g3CfPXPY1J3>R>,<=,3Y95Y]P:1C3IRI%TB5S3RB9K3=R]AK3>B'<,3YC=P;P^b3b4b5X03X:3X1T1025,161>5JRB1>6J'0[^03^:3^1TP2104A14AC'1PAf8P<O4b2O3b6CHAB78bP7P8%A8?8OFX;7PEPaP2ELb6PNP2ELb6PRPVPUPWPXPY1C3C,E=,3Y95Y[=5Y\R\P:1EZ],3Y%T?9S3IRI,<],3Y55YR]C=P;P^b3b4b5X03X1T142C,1_/15R_144B10BL'1RB[^03^1TP210GHPHP5O3RCb29NQLE?PMPVPUPWPXPY1EZ=,3YRZ1C3@,<=,3Y55YRMP:P]C=P;P^b3b4b5X031442102@'1R@PB[^03P2PGP1O2RGb29NKLE?191JPVPUPWPXPYP\P:1<=I,3Y95YZRZC=P;P^b3b4b5X03X1T105L,19R9\_^03^1TPCb2,Q1E?PPPVPUPWPXPYPMP:PZC=P;P^b3b4b5X03P9\@^03PGb2,QHE?W8P2O1n200100000021100011000W6W?X>3X@3o"). Qed.
End CANSEC1.
