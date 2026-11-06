(* diginet_scribble_text in image B (fuzz_codec.asan-ubsan, 0x86500): the segment Ha of
   diginet_scribble_text_B_inv.v -- one pass of the first loop from the loop head 0x86544 up to the padding
   0x8664c, the store of a byte that is not '.' and a digit (0x865c4), or the loop head again after a '.' and a
   digit 1..9 (sc_seg_Ha).

   The code: 0x86544 a4 := a3 + a0 = q + i (pinned to atom 33 at 0x86548); the instrumented check of a4 (paid by the
   shadow entry of atom 33); lbu t4 := b = q[i]; b = 0 or j >= n go to 0x8664c. Else 0x86564 andi/bnez t5 (the
   UBSan check on t5 = 0: decided); b <> '.' goes to 0x865c4. For b = '.': t6 := a0 + t0 = q + i + 1, bltu t6,a3
   (UBSan, not taken: no wrap); a4 := q + i + 1, its instrumented check (atom 33's entry covers two bytes), lbu t5 :=
   b2 = q[i + 1]; b2 < '1' goes to 0x865c4; beqz t6 (UBSan, decided: t6 >= 2); b2 > '9' goes to 0x865c4; bltu a6,a7
   (UBSan on o + j, decided by the ranges); a4 := a1 + a7 = o + j (pinned to atom 36 at 0x865a4), its instrumented
   check, sb t5 - 26 at o + j; a4 := 2; then the advance of i (by 2) and j and the UBSan check of q + i + 2 (bgeu,
   not taken: no wrap) back to 0x86544.
   The state: the text bytes at q + i (one when b = 0 or j >= n, else two) read only; the byte o + j writable when
   j < n. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_scribble_text_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
(* a register the run did not write: its atom, the boundary's register; a5 is pinned to atom 32 *)
Ltac skeep := sreg; rewrite ?sv_denot_SOff0; ewpeel;
  first [ lazymatch goal with EE : forall n (rr : bv 5), _ -> ew ?Ev n = _ |- _ => apply EE; reflexivity end
        | lazymatch goal with E32 : ew _ 32 = _, R15 : getr _ 15 = w64 SHADOW_OFF |- _ =>
            rewrite E32, R15; reflexivity end ].
Ltac kio := first [ apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio ].
(* the write windows of a state: none, or the byte o + j of atom 36, which the caller lets the call write *)
Ltac sa_awr := cbn [ss_mem];
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | lazymatch goal with
    | TWj : twr_ok _ ?Bv ?STK ?sp0 ?FP ?ly ?S ?lyc ?Sc ?own ?W ?memc ?sp ?q 1, U36 : bv_unsigned (ew _ 36) = ?q |- _ =>
      eapply (cw_awr_ok_cons_twr Bv _ _ _ STK sp0 FP ly S lyc Sc own W memc sp q 1 36%nat);
      [reflexivity | ewpeel; exact U36 | cbn; lia | cbn; lia | exact TWj | ] end ].
(* fold a run's growth into KP and its frame into KE (zone: the byte o + j of atom 36, or none) *)
Ltac sa_keep :=
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2),
                      KP : forall a, apresent ?H ?m0 a -> apresent ?H ?m1 a |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H m0 a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end;
  cw_keep ltac:(let a := fresh "a" in let rr := fresh "rr" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
    intros a (rr & Hr & Hb); cbv beta;
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rr rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
        first [ lia | lazymatch goal with U36 : bv_unsigned (ew _ 36) = _ |- _ => rewrite U36 in Hb end; lia ] | ]);
    destruct Hr).
(* pin a4 to atom n, which holds a + b of the two atoms the add read *)
Ltac sa_pin n ra rb va vb Ea Eb En :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
    pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (14%bv : bv 5) (SOff n 0) HS eq_refl
      ltac:(cbn [ms_regs restrict]; sreg; rewrite sv_denot_SOff0; ewpeel; rewrite En; symmetry;
            rewrite (denot_add2 Ev ra rb va vb ltac:(ewpeel; exact Ea) ltac:(ewpeel; exact Eb)
                       ltac:(lia) ltac:(lia) ltac:(lia)); f_equal; lia))
      as YS; clear HS; rename YS into HS; norm_ss HS end.

(* a branch condition as Z: the atoms of the state's registers, its literals, the sums the code forms *)
Ltac sa_cond Hc Ei Eq Eq1 Ej En Eb Eb2 Eo ii qq jj nn bb bb2 oo :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U, ?branch_geu_U in Hc;
    repeat (rewrite U_SAlu in Hc; cbn [zalu_raw] in Hc);
    rewrite ?(U_atom Ev 10 ii ltac:(ewpeel; exact Ei) ltac:(lia)) in Hc;
    rewrite ?(U_atom_off Ev 10 ii 2 ltac:(ewpeel; exact Ei) ltac:(lia) ltac:(lia)) in Hc;
    rewrite ?(U_atom Ev 13 qq ltac:(ewpeel; exact Eq) ltac:(lia)) in Hc;
    rewrite ?(U_atom Ev 5 (qq + 1) ltac:(ewpeel; exact Eq1) ltac:(lia)) in Hc;
    rewrite ?(U_atom Ev 17 jj ltac:(ewpeel; exact Ej) ltac:(lia)) in Hc;
    rewrite ?(U_atom Ev 12 nn ltac:(ewpeel; exact En) ltac:(lia)) in Hc;
    rewrite ?(U_atom Ev 34 bb ltac:(ewpeel; exact Eb) ltac:(lia)) in Hc;
    rewrite ?(U_atom Ev 35 bb2 ltac:(ewpeel; exact Eb2) ltac:(lia)) in Hc;
    rewrite ?U_lit in Hc by lia;
    rewrite ?zcanon_id in Hc by (unfold M64; lia) end.

Definition sa_rt1 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition sa_rt2 : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0))].
Definition sa_rout : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
Definition sa_srA : list sv := sr_set sr_atoms 15%bv (SOff 32 0).
Definition sa_srB : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 15%bv (SOff 32 0)) 30%bv (SLit 0)) 6%bv (SLit 46)) 7%bv (SLit 49))
    28%bv (SLit 57).
Definition sa_GA (lo hi : Z) : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 (2 ^ 47 - 2) 0); (34%nat, mkAF lo hi 0);
           (10%nat, mkAF 0 (2 ^ 47 - 2) 0); (13%nat, mkAF 1 (2 ^ 47 - 2) 0); (17%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (12%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition sa_GB : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 (2 ^ 47 - 3) 0); (34%nat, mkAF 1 255 0); (35%nat, mkAF 0 255 0);
           (36%nat, mkAF 1 (2 ^ 47 - 2) 0); (10%nat, mkAF 0 (2 ^ 47 - 3) 0); (13%nat, mkAF 1 (2 ^ 47 - 2) 0);
           (5%nat, mkAF 2 (2 ^ 47 - 1) 0); (17%nat, mkAF 0 (2 ^ 32 - 2) 0); (12%nat, mkAF 1 (2 ^ 32 - 1) 0);
           (11%nat, mkAF 1 (2 ^ 47 - 2) 0); (16%nat, mkAF (2 ^ 63 - 1) (2 ^ 64 - 2) 0)] [] [].

(* the result after a byte that is not '.' followed by a digit 1..9 *)
Lemma sa_spec_other : forall (res : list Z * Z) tb i j n outs b b2,
  (S (Z.to_nat i) < length tb)%nat -> nth (Z.to_nat i) tb 0 = b -> nth (S (Z.to_nat i)) tb 0 = b2 -> b <> 0 ->
  0 <= i -> 0 <= j < n -> ((b =? 46) && (49 <=? b2) && (b2 <=? 57)) = false ->
  res = (outs ++ fst (scr_lib (skipn (Z.to_nat i) tb) (Z.to_nat (n - j))),
         i + snd (scr_lib (skipn (Z.to_nat i) tb) (Z.to_nat (n - j)))) ->
  res = ((outs ++ [if b <? 128 then b else 63]) ++ fst (scr_lib (skipn (Z.to_nat i + 1) tb) (Z.to_nat (n - (j + 1)))),
         (i + 1) + snd (scr_lib (skipn (Z.to_nat i + 1) tb) (Z.to_nat (n - (j + 1))))).
Proof.
intros res tb i j n outs b b2 Hl H1 H2 Hb Hi Hj Hc ->.
replace (Z.to_nat (n - j)) with (S (Z.to_nat (n - (j + 1)))) by lia.
rewrite (sc_lib_next tb (Z.to_nat i) _ Hl ltac:(rewrite H1; exact Hb)), H1, H2, Hc. cbn [fst snd].
rewrite Nat.add_1_r, <- app_assoc. cbn [app]. f_equal. lia.
Qed.
(* the result after '.' and a digit 1..9 *)
Lemma sa_spec_dot : forall (res : list Z * Z) tb i j n outs b b2,
  (S (Z.to_nat i) < length tb)%nat -> nth (Z.to_nat i) tb 0 = b -> nth (S (Z.to_nat i)) tb 0 = b2 -> b <> 0 ->
  0 <= i -> 0 <= j < n -> ((b =? 46) && (49 <=? b2) && (b2 <=? 57)) = true ->
  res = (outs ++ fst (scr_lib (skipn (Z.to_nat i) tb) (Z.to_nat (n - j))),
         i + snd (scr_lib (skipn (Z.to_nat i) tb) (Z.to_nat (n - j)))) ->
  res = ((outs ++ [b2 - 26]) ++ fst (scr_lib (skipn (Z.to_nat (i + 2)) tb) (Z.to_nat (n - (j + 1)))),
         (i + 2) + snd (scr_lib (skipn (Z.to_nat (i + 2)) tb) (Z.to_nat (n - (j + 1))))).
Proof.
intros res tb i j n outs b b2 Hl H1 H2 Hb Hi Hj Hc ->.
replace (Z.to_nat (n - j)) with (S (Z.to_nat (n - (j + 1)))) by lia.
rewrite (sc_lib_next tb (Z.to_nat i) _ Hl ltac:(rewrite H1; exact Hb)), H1, H2, Hc. cbn [fst snd].
replace (Z.to_nat (i + 2)) with (S (S (Z.to_nat i))) by lia.
rewrite <- app_assoc. cbn [app]. f_equal. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem sha_holds : sc_seg_Ha B.
Proof.
unfold sc_seg_Ha. intros g fuel W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPH).
destruct HPH as (i & j & outs & R10 & R17 & R11 & R13 & R5 & R6 & R7 & R28 & R30 & Hi & Hin & Hf & Hj & Hlen & Hout &
  Hspec).
destruct (sc_text B g Hpre) as (Hq0 & Hql & Hin0 & Hlen0 & HG & HRAq & Hamq & Hoffq).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hamo & HDJ).
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof (sc_amem47 (sg_q g) (sg_len g) ltac:(lia) ltac:(lia) Hamq) as Hq47.
pose proof HC as (_ & _ & R12 & R15 & R16 & _ & _ & KC & PC).
assert (Hil : (Z.to_nat i < length (sg_tb g))%nat) by exact (sc_in_skipn_lt 0 _ _ Hin).
unfold sg_len in *.
set (bt := nth (Z.to_nat i) (sg_tb g) 0).
set (bt2 := nth (Z.to_nat i + 1) (sg_tb g) 0).
destruct (sc_text_val B g mem2 Hpre KC (Z.to_nat i) Hil) as (Vbt & Rbt). fold bt in Vbt, Rbt.
rewrite Z2Nat.id in Vbt by lia.
set (E := Ereg regs2 (cw_extra [sg_q g + i; bt; bt2; sg_o g + j])).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros nn rr Hnn; unfold E; apply ew_Ereg_nat; exact Hnn).
assert (E5 : ew E 5 = Z_to_bv 64 (sg_q g + 1)) by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E10 : ew E 10 = Z_to_bv 64 i) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 (sg_q g)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E16 : ew E 16 = Z_to_bv 64 (sg_noto g)) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E17 : ew E 17 = Z_to_bv 64 j) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (sg_q g + i)) by (exact (cw_ew_x regs2 [sg_q g + i; bt; bt2; sg_o g + j] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 bt) by (exact (cw_ew_x regs2 [sg_q g + i; bt; bt2; sg_o g + j] 1)).
assert (E35 : ew E 35 = Z_to_bv 64 bt2) by (exact (cw_ew_x regs2 [sg_q g + i; bt; bt2; sg_o g + j] 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (sg_o g + j)) by (exact (cw_ew_x regs2 [sg_q g + i; bt; bt2; sg_o g + j] 3)).
assert (U33 : bv_unsigned (ew E 33) = sg_q g + i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sg_o g + j <= a < sg_o g + j + 1 /\ j < sg_n g) ->
  aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) mem2 a) by (intros; assumption).
assert (RAt : forall m, 0 <= m -> i + m <= Z.of_nat (length (sg_tb g)) ->
  range_addressable (aview tfibsegs (w_H (sg_W g)) mem2) SHADOW_OFF (sg_q g + i) m).
{ intros m Hm0 Hm. apply (sc_ra_kept B g mem2 Hpre KC); [lia | lia | |].
  - unfold amem_range in Hamq |- *. rewrite C3, C4, C5 in *. lia.
  - eapply range_addressable_sub; [exact HRAq | lia | lia]. }
unfold cfg_at. change (w64 PC_H) with (Z_to_bv 64 PC_H).
destruct (Z.eq_dec bt 0) as [Hz | Hnz]; [|destruct (Z_lt_le_dec j (sg_n g)) as [Hjn | Hjn]].
3: assert (HAB : bt = 0 \/ j = sg_n g) by lia.
1: assert (HAB : bt = 0 \/ j = sg_n g) by lia.
(* ======== b = 0 or j = n: to the padding ======== *)
1, 3:
  assert (HSA : forall lo hi, lo <= bt <= hi -> 0 <= lo -> hi <= 255 ->
    st_ok tfibsegs E (mkSS PC_H sa_srA [sa_rt1] None (sa_GA lo hi))
      (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_H) mem2 (seg_rom tfibsegs))));
  [ intros lo hi Hb1 Hlo Hhi;
    rewrite restrict_mkst_fx; apply entry_st_ok_full; change (Ereg regs2 (cw_extra [sg_q g + i; bt; bt2; sg_o g + j])) with E;
    [ unfold sa_srA; apply regs_ok_pin; [apply regs_ok_Ereg | discriminate |]; rewrite sv_denot_SOff0, E32; exact R15
    | reflexivity
    | apply Forall_cons; [|apply Forall_nil];
      unfold region_ok, sa_rt1; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite U33; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val tfibsegs E _ (sg_q g + i) 0 1 (SOff 34 0) bt);
      [ rewrite sv_denot_SOff0; exact E34 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vbt ]
    | cbn [pairwise_disjoint all_disjoint]; tauto
    | split; [|split; exact I]; unfold sa_GA; cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
      rewrite E32, U33, E34, E10, E13, E17, E12; rewrite !unsigned_lit_small by (unfold SB; lia);
      rewrite !Z.pow_0_r, !Z.mod_1_r; unfold SB; repeat split; first [exact I | lia] ]
  | ];
  clearbody E;
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 1] E (mrestrict (w_H (sg_W g)) mem2));
  [ apply Forall_cons; [|apply Forall_nil];
    apply (cw_shent_ra (sg_W g) mem2 E 33 (sg_q g + i) 1 (RAt 1 ltac:(lia) ltac:(lia)));
    [ unfold amem_range in Hamq |- *; rewrite C3, C4, C5 in *; lia | lia | lia | lia | exact E33 | exact E32 ]
  | ].
1: pose proof (HSA 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
2: pose proof (HSA 1 255 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
1, 2: clear HSA; cw_run_to sa_awr 0x86548; sa_keep; sa_pin 33%nat 10%nat 13%nat i (sg_q g) E10 E13 E33.
2: cw_run sa_awr; sa_keep; cw_branch Hb;
   lazymatch type of Hb with branch_taken _ (sv_denot ?Ev _) _ = _ =>
     rewrite branch_geu_U, (U_atom Ev 17 j ltac:(ewpeel; exact E17) ltac:(lia)),
       (U_atom Ev 12 (sg_n g) ltac:(ewpeel; exact E12) ltac:(lia)) in Hb end.
3: apply negb_false_iff, Z.ltb_lt in Hb; exfalso; lia.
2: cw_run_to sa_awr PC_P; sa_keep.
1: cw_run sa_awr; sa_keep; cw_branch Hb0;
   lazymatch type of Hb0 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
     rewrite branch_eq_U, (U_atom Ev 34 bt ltac:(ewpeel; exact E34) ltac:(lia)), U_lit in Hb0 by lia end.
2: apply Z.eqb_neq in Hb0; exfalso; exact (Hb0 Hz).
1: cw_run_to sa_awr PC_P; sa_keep.
1, 2:
  apply SRr_ret; right; left;
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_P (P_P g) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ kio
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha Hz'; apply KE; [exact Ha | lia]
    | exact KP | ] end;
  exists i, j, outs;
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E10|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E17|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E11|];
  split; [lia|]; split; [exact Hlen|];
  split; [apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout];
          intros x Hx; apply (mbyte_of_aview tfibsegs); apply KE; lia|].
1: rewrite Hspec, (sc_lib_at_zero (sg_tb g) (Z.to_nat i) _ Hil Hz), Z.add_0_r; reflexivity.
1: replace (sg_n g - j) with 0 in Hspec |- * by lia; rewrite Hspec, sc_lib_0, Z.add_0_r; reflexivity.
(* ======== b <> 0 and j < n ======== *)
assert (Hil1 : (Z.to_nat i + 1 < length (sg_tb g))%nat)
  by (pose proof (sc_in_skipn_lt 0 _ _ (sc_in0_S (sg_tb g) (Z.to_nat i) Hin Hnz)); lia).
destruct (sc_text_val B g mem2 Hpre KC (Z.to_nat i + 1) Hil1) as (Vbt2 & Rbt2). fold bt2 in Vbt2, Rbt2.
replace (sg_q g + Z.of_nat (Z.to_nat i + 1)) with (sg_q g + i + 1) in Vbt2 by lia.
assert (U36 : bv_unsigned (ew E 36) = sg_o g + j) by (rewrite E36; apply unsigned_lit_small; lia).
assert (Hpj : forall a, sg_o g + j <= a < sg_o g + j + 1 -> apresent (w_H (sg_W g)) mem2 a)
  by (intros a Ha; apply (sc_out_present B g mem2 Hpre PC); lia).
assert (RAj : range_addressable (aview tfibsegs (w_H (sg_W g)) mem2) SHADOW_OFF (sg_o g + j) 1).
{ apply (sc_ra_kept B g mem2 Hpre KC); [lia | lia | |].
  - unfold amem_range in Hamo |- *. rewrite C3, C4, C5 in *. lia.
  - eapply range_addressable_sub; [exact HRAo | lia | lia]. }
assert (TWj : twr_ok tfibsegs B (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g) (sg_S g) (sg_lyc g) (sg_Sc g) (sg_own g)
  (sg_W g) (sg_memc g) (sg_sp g) (sg_o g + j) 1) by (intros a Ha; apply HTW; lia).
assert (HS : st_ok tfibsegs E (mkSS PC_H sa_srB [sa_rt2; sa_rout] None sa_GB)
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_H) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full; change (Ereg regs2 (cw_extra [sg_q g + i; bt; bt2; sg_o g + j])) with E.
  - unfold sa_srB.
    repeat (apply regs_ok_pin; [ | discriminate | ]); [apply regs_ok_Ereg | | | | | ].
    + rewrite sv_denot_SOff0, E32. exact R15.
    + rewrite R30. reflexivity.
    + rewrite R6. reflexivity.
    + rewrite R7. reflexivity.
    + rewrite R28. reflexivity.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, sa_rt2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val tfibsegs E _ (sg_q g + i) 0 1 (SOff 34 0) bt);
        [ rewrite sv_denot_SOff0; exact E34 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vbt ].
      * apply (chunk_ok_val tfibsegs E _ (sg_q g + i) 1 1 (SOff 35 0) bt2);
        [ rewrite sv_denot_SOff0; exact E35 | cbn; lia | cbn; lia | exact Vbt2 ].
    + unfold region_ok, sa_rout. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U36. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros a Ha. apply (apresent_writable tfibsegs). apply Hpj. lia.
  - apply pairwise_disjoint_of_extents. unfold sa_rt2, sa_rout, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U36.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. unfold sa_GB. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U33, E34, E35, U36, E10, E13, E5, E17, E12, E11, E16. unfold sg_noto.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; first [exact I | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 2; mkSHE 36 0 1] E (mrestrict (w_H (sg_W g)) mem2)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (cw_shent_ra (sg_W g) mem2 E 33 (sg_q g + i) 2 (RAt 2 ltac:(lia) ltac:(lia)));
    [ unfold amem_range in Hamq |- *; rewrite C3, C4, C5 in *; lia | lia | lia | lia | exact E33 | exact E32 ].
  - apply (cw_shent_ra (sg_W g) mem2 E 36 (sg_o g + j) 1 RAj);
    [ unfold amem_range in Hamo |- *; rewrite C3, C4, C5 in *; lia | lia | lia | lia | exact E36 | exact E32 ]. }
cw_run_to sa_awr 0x86548. sa_keep. sa_pin 33%nat 10%nat 13%nat i (sg_q g) E10 E13 E33.
cw_run sa_awr. sa_keep.
(* 0x86560 bgeu a7,a2: j < n *)
cw_branch Hb. all: sa_cond Hb E10 E13 E5 E17 E12 E34 E35 E11 i (sg_q g) j (sg_n g) bt bt2 (sg_o g).
1: apply negb_true_iff, Z.ltb_ge in Hb; exfalso; lia.
apply negb_false_iff, Z.ltb_lt in Hb.
(* the check on t5 (decided), to bne t4,t1 at 0x8656c *)
cw_run sa_awr. sa_keep.
cw_branch Hd. all: sa_cond Hd E10 E13 E5 E17 E12 E34 E35 E11 i (sg_q g) j (sg_n g) bt bt2 (sg_o g).
(* taken: b <> '.', to 0x865c4; else the '.' path *)
2: apply negb_false_iff, Z.eqb_eq in Hd.
2: cw_run sa_awr; sa_keep; cw_branch H1; sa_cond H1 E10 E13 E5 E17 E12 E34 E35 E11 i (sg_q g) j (sg_n g) bt bt2 (sg_o g).
3: apply Z.ltb_ge in H1.
2: apply Z.ltb_lt in H1; exfalso; lia.
(* goal 2: the check of q + i + 1 done, lbu t5 = b2, stop at bltu t5,t2 *)
2: cw_run sa_awr; sa_keep; cw_branch H2; sa_cond H2 E10 E13 E5 E17 E12 E34 E35 E11 i (sg_q g) j (sg_n g) bt bt2 (sg_o g).
(* goal 3: b2 >= '1' *)
3: apply Z.ltb_ge in H2; cw_run sa_awr; sa_keep; cw_branch H3; sa_cond H3 E10 E13 E5 E17 E12 E34 E35 E11 i (sg_q g) j (sg_n g) bt bt2 (sg_o g).
(* goal 4: b2 <= '9': the store of b2 - 26 *)
4: apply Z.ltb_ge in H3; cw_run_to sa_awr 0x865a4; sa_keep;
   sa_pin 36%nat 11%nat 17%nat (sg_o g) j E11 E17 E36;
   cw_run sa_awr; sa_keep; cw_branch H4; sa_cond H4 E10 E13 E5 E17 E12 E34 E35 E11 i (sg_q g) j (sg_n g) bt bt2 (sg_o g).
5: apply negb_false_iff, Z.ltb_lt in H4; exfalso; lia.
4: apply negb_true_iff, Z.ltb_ge in H4; cw_run_to sa_awr PC_H; sa_keep;
   assert (Hcnd1 : ((bt =? 46) && (49 <=? bt2) && (bt2 <=? 57)) = true)
     by (rewrite Hd; rewrite (proj2 (Z.leb_le 49 bt2) ltac:(lia)), (proj2 (Z.leb_le bt2 57) ltac:(lia)); reflexivity);
   assert (Hb2' : nth (S (Z.to_nat i)) (sg_tb g) 0 = bt2) by (unfold bt2; rewrite Nat.add_1_r; reflexivity);
   pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG; cbn [ms_mem restrict] in RG;
   lazymatch type of RG with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG end;
   lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ =>
     assert (Vv : val_mem tfibsegs (mrestrict (w_H (sg_W g)) (ms_mem msv)) (sg_o g + j) 1 (bt2 - 26)) end;
   [ first
     [ pose proof (field_of_region _ _ 36 (sg_o g + j) _ 0 1 0 1 0 1%N (SOff 35 (-26)) (bt2 - 26) RG
         ltac:(ewpeel; exact U36) ltac:(apply in_eq)
         ltac:(cbn [sv_denot]; ewpeel; rewrite E35, unsigned_lit_small by lia; f_equal; lia)
         ltac:(cbn; lia) ltac:(cbn; lia)) as V0; rewrite Z.add_0_r in V0; exact V0
     ]
   | ];
   apply SRr_ret; left;
   lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
     apply (sc_cut_close B g PC_H (P_H g fuel) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
     [ kio
     | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
     | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
     | intros a Ha Hz'; apply KE; [exact Ha | lia]
     | exact KP | ] end;
   exists (i + 2), (j + 1), (outs ++ [bt2 - 26]);
   split; [sreg; cbn [sv_denot]; ewpeel; rewrite E10, unsigned_lit_small by lia; reflexivity|];
   split; [sreg; cbn [sv_denot]; ewpeel; rewrite E17, unsigned_lit_small by lia; reflexivity|];
   split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E11|];
   split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E13|];
   split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E5|];
   split; [sreg; reflexivity|];
   split; [sreg; reflexivity|];
   split; [sreg; reflexivity|];
   split; [sreg; reflexivity|];
   split; [lia|];
   split; [replace (Z.to_nat (i + 2)) with (S (S (Z.to_nat i))) by lia;
           apply sc_in0_S; [exact (sc_in0_S _ _ Hin Hnz) | rewrite Hb2'; lia]|];
   split; [unfold sg_len; lia|]; split; [lia|];
   split; [rewrite length_app; cbn [length]; lia|];
   split;
   [ apply sc_garr8_snoc;
     [ apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout];
       intros x Hx; apply (mbyte_of_aview tfibsegs); apply KE; lia
     | rewrite Hlen; exact Vv | lia ] |];
   exact (sa_spec_dot (sc_res g) (sg_tb g) i j (sg_n g) outs bt bt2 ltac:(lia) eq_refl Hb2' Hnz Hi ltac:(lia) Hcnd1
            Hspec).
(* goals 1, 2, 3: to 0x865c4 with t4 = b *)
1: apply negb_true_iff, Z.eqb_neq in Hd.
2: apply Z.ltb_lt in H2.
3: apply Z.ltb_lt in H3.
1, 2, 3: assert (Hcnd : ((bt =? 46) && (49 <=? bt2) && (bt2 <=? 57)) = false)
  by (destruct (Z.eqb_spec bt 46); destruct (Z.leb_spec 49 bt2); destruct (Z.leb_spec bt2 57); cbn; try reflexivity; lia).
1, 2, 3: cw_run_to sa_awr PC_O; sa_keep.
1, 2, 3:
  apply SRr_ret; right; right;
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_O (P_O g fuel) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ kio
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha Hz'; apply KE; [exact Ha | lia]
    | exact KP | ] end;
  exists i, j, bt, outs;
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E10|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E17|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E11|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E13|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E5|];
  split; [sreg; reflexivity|];
  split; [sreg; reflexivity|];
  split; [sreg; reflexivity|];
  split; [sreg; rewrite sv_denot_SOff0; ewpeel; exact E34|];
  split; [lia|]; split; [reflexivity|]; split; [exact Hnz|];
  split; [rewrite Nat.add_1_r; exact (sc_in0_S _ _ Hin Hnz)|];
  split; [unfold sg_len; lia|]; split; [lia|]; split; [exact Hlen|];
  split; [apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout];
          intros x Hx; apply (mbyte_of_aview tfibsegs); apply KE; lia|];
  exact (sa_spec_other (sc_res g) (sg_tb g) i j (sg_n g) outs bt bt2 ltac:(lia) eq_refl
           ltac:(unfold bt2; rewrite Nat.add_1_r; reflexivity) Hnz Hi ltac:(lia) Hcnd Hspec).
Time Qed.
End h.
End d.
