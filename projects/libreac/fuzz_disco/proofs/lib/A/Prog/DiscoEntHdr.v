(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 453 of its 485 lines of code are new or changed and 37 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntShChk DiscoEntHdrLib DiscoEntHdrCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma hd_cell_mono : forall p n x y, p mod 8 = 0 -> p <= x <= y -> dsh_cell p n x <> 0 -> dsh_cell p n y <> 0.
Proof.
intros p n x y Hp Hxy H. unfold dsh_cell in *.
destruct (Z.ltb_spec ((x - p) / 8) (n / 8)); [lia|].
pose proof (Z.div_le_mono (x - p) (y - p) 8 ltac:(lia) ltac:(lia)).
destruct (Z.ltb_spec ((y - p) / 8) (n / 8)); [lia | exact H].
Qed.
Lemma hd_w64_sext : forall b, 0 <= b < 256 ->
  Z_to_bv 64 (if b <? 128 then b else b + (2 ^ 64 - 256)) = w64 (if b <? 128 then b else b - 256).
Proof.
intros b Hb. unfold w64. destruct (b <? 128); [reflexivity|]. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
replace (b - 256) with ((b + (2 ^ 64 - 256)) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Section u.
Variable E : env.
Lemma hd_beq_cell : forall v s, ew E v = Z_to_bv 64 s -> 0 <= s < 8 ->
  branch_taken BC_EQ (sv_denot E (SExt true 8 (SOff v 0))) (sv_denot E (SLit 0)) = (s =? 0).
Proof.
intros v s Hv Hs. rewrite branch_eq_U, (hd_U_sext8 E v s Hv) by lia. rewrite U_lit by lia.
destruct (Z.ltb_spec s 128); [reflexivity | lia].
Qed.
Lemma hd_bge_cell : forall k c x v s, ew E k = Z_to_bv 64 x -> 0 <= x -> 0 <= c -> x + c < 2 ^ 64 ->
  ew E v = Z_to_bv 64 s -> 0 <= s < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff k c) (SLit 7))) (sv_denot E (SExt true 8 (SOff v 0)))
  = negb ((x + c) mod 8 <? s).
Proof.
intros k c x v s Hk Hx Hc Hxc Hv Hs. rewrite hd_br_ge, (hd_S_and7 E k c x Hk Hx Hc Hxc), (hd_S_sext8 E v s Hv) by lia.
destruct (Z.ltb_spec s 128); [reflexivity | lia].
Qed.
Lemma hd_U_mul : forall X dt, U E X = dt -> 0 <= dt < 65536 -> U E (SMd M_MUL X (SLit 1000000)) = dt * 1000000.
Proof.
intros X dt HX Rdt. rewrite U_SMd. cbn [zmd_raw]. rewrite HX, U_SLit. change (zcanon 1000000) with 1000000.
apply zcanon_id. unfold M64. lia.
Qed.
End u.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Lemma hdr_land_mid : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state) (n' pc : Z)
  (P : bvmap 5 word -> Prop) (Q : Prop),
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 232 <= a < d_A cx + 352) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a) ->
  0 <= n' <= n ->
  P (ms_regs ms) -> Q ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc (EV_HEAD i) (ACC_HEAD MT i)
    (fun regs ly3' S3' W3' mem3' md3' =>
       Q /\ P regs /\ d_body B cx h n' [] dsh_loop ly3' S3' W3' mem3')
    W3 (mkCfg ms md').
Proof.
intros fq cx h i n now ly3 S3 W3 mem3 md' k acc E ss ms n' pc P Q
  HB HFQ HJ HFR Hk Hev Hmo Hacc HE HFL HS Hrv Hpc Hchk HBD MEQ MPR Hn' HP HQ.
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (hd_A_range cx HS608) as [HAr _].
pose proof HBD as (T & G & Lk & H & HFRM & _).
pose proof HFRM as (E0 & _ & _ & _ & V216 & V152).
assert (V216' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 216) 8 h).
{ apply (hd_val_mem_keep (w_H W3) mem3 (ms_mem ms) (d_A cx + 216) 8 h V216). intros j Hj. apply MEQ; [|lia].
  unfold d_S, LLVMF_STK in *. lia. }
assert (V152' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 152) 8 (h + 440)).
{ apply (hd_val_mem_keep (w_H W3) mem3 (ms_mem ms) (d_A cx + 152) 8 (h + 440) V152). intros j Hj. apply MEQ; [|lia].
  unfold d_S, LLVMF_STK in *. lia. }
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_loop ly3 S3 W3 md' k E ss ms (conj HB (conj HJ HFR)) HE HFL HS Hchk V216' V152')
  as [HFRM' HSHD'].
assert (HBD' : d_body B cx h n' [] dsh_loop ly3 S3 W3 (ms_mem ms)).
{ apply (d_body_keep B cx h n n' dsh_loop ly3 S3 W3 mem3 (ms_mem ms) (d_A cx + 232) (d_A cx + 352) HBD).
  - unfold d_S, LLVMF_STK in *. lia.
  - lia.
  - exact MEQ.
  - intros a _ Ha. exact (MPR a Ha).
  - exact HFRM'.
  - exact HSHD'.
  - exact Hn'. }
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFQ|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact HQ|]. split; [exact HP|]. exact HBD'.
Qed.

Ltac hew := cbn [ew havoc d_env AT_FL Nat.ltb Nat.leb Nat.sub nth hdr_vals].
Ltac hew_in H := cbn [ew havoc d_env AT_FL Nat.ltb Nat.leb Nat.sub nth hdr_vals] in H.
Ltac hval Ex k :=
  let t := eval cbn [ew havoc d_env AT_FL Nat.ltb Nat.leb Nat.sub nth hdr_vals] in (ew Ex k) in
  lazymatch t with Z_to_bv 64 ?z => z | w64 ?z => z end.
Ltac hside := first [ hew; first [ reflexivity | assumption ] | lia | unfold d_cur, dsh_cell_addr, SHADOW_OFF; lia ].
Ltac hrewU := repeat match goal with
  | U : bv_unsigned (ew ?E0 ?q) = _ |- context [bv_unsigned (ew ?E0 ?q)] => rewrite U end.

Ltac hawr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn [In] in Hin;
  repeat (destruct Hin as [ <- | Hin ];
    [ cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi fshadow_region got_regionP bcell_regionP hdr_in dsh_cell_region] in Ha;
      first [ exfalso; lia | left; revert Ha; hew; hrewU; intros Ha; unfold LLVMF_STK; lia ] | ]);
  destruct Hin.

Ltac hwin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | revert Ha; hew; hrewU; intros Ha; lia ] | ]);
  destruct Hin.

Ltac hupd :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m1) (mrestrict _ ?m2),
    MEQ : forall a, _ -> ~ (?lo <= a < ?hi) -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (hd_meq_frame Eo rs Hh m0 m1 m2 lo hi HFr ltac:(hwin) MEQ) as MEQ2; clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with
  | HG : mem_grows (mrestrict ?Hh ?m1) (mrestrict _ ?m2), MPR : forall a, apresent _ ?m0 a -> apresent _ ?m1 a |- _ =>
    let MPR2 := fresh "MPR" in pose proof (hd_pres_grow Hh m0 m1 m2 HG MPR) as MPR2; clear MPR; rename MPR2 into MPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac hrun RUNTO stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ (restrict (w_H _) _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; [ hawr | hupd ]
  end.

Ltac hdrop :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss ?ms |- _ =>
    let L := eval vm_compute in (ss_mem ss) in
    lazymatch L with
    | YP09.mkRegion (Some ?q0) 0 1 0 0 _ :: ?rest =>
      lazymatch eval vm_compute in (Nat.leb 560 q0) with
      | true =>
        let HS2 := fresh "HS" in
        pose proof (st_ok_pi_submem Ec ss ms rest HS (submem_drop rest _ rest (submem_refl rest)) ltac:(vm_compute; reflexivity)) as HS2;
        clear HS; rename HS2 into HS; norm_ss HS
      | false => idtac
      end
    | _ => idtac
    end
  end.

Ltac hdisj :=
  apply all_disjoint_of_extents; unfold dsh_cell_region, extent_of_region;
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]; unfold zdisj; cbn [fst snd];
  hew; hrewU; unfold w64; rewrite ?unsigned_lit_small by hside;
  unfold dsh_cell_addr, shadow_addr, SHADOW_OFF; unfold d_cur;
  repeat match goal with
  | H : in_app _ _ |- _ => unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H
  | H : zdisjoint _ _ |- _ => unfold zdisjoint in H; cbn [fst snd] in H
  end;
  try (unfold IMG_LO, IMG_TOP in *); repeat split; lia.

Ltac hcell j rd q v cx n :=
  hdrop;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
    let EQq := fresh "EQq" in let EQv := fresh "EQv" in
    add_atom HS q (Z_to_bv 64 (dsh_cell_addr (d_cur cx n + j))) EQq;
    add_atom HS v (Z_to_bv 64 (dsh_cell (c_p cx) (c_n cx) (d_cur cx n + j))) EQv;
    clear EQq EQv
  end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly ?S _ ?mm ?md _ |- _ =>
    let R := fresh "R" in
    pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms rd HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) rd) in change (sr_get (ss_regs ss) rd) with e in R;
    rewrite (dsh_cell_denot Ec 531 q j (d_cur cx n)) in R by hside;
    let HS2 := fresh "HS" in
    pose proof (dsh_cell_seat Ec ss ms W rd q v (dsh_cell_addr (d_cur cx n + j))
      (dsh_cell (c_p cx) (c_n cx) (d_cur cx n + j)) HS ltac:(vm_compute; reflexivity) (eq_sym R)
      ltac:(hew; reflexivity) ltac:(hside) ltac:(hew; reflexivity)
      ltac:(pose proof (dsh_cell_range (c_p cx) (c_n cx) (d_cur cx n + j)); lia)
      (dsh_cell_val B LAWS ly S W mm md (c_p cx) (c_n cx) (d_cur cx n + j) (proj1 HJ) ltac:(assumption) ltac:(unfold d_cur; lia))
      ltac:(hdisj)) as HS2;
    clear HS R; rename HS2 into HS; norm_ss HS
  end;
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict (w_H ?W) ?ms), SHOK : sh_ok _ _ _ _ _ |- _ =>
    clear SHOK;
    pose proof (Forall_nil (shent_ok SEGS (SOff 32 0) Ec (mrestrict (w_H W) (ms_mem ms))) :
      sh_ok SEGS (SOff 32 0) [] Ec (mrestrict (w_H W) (ms_mem ms))) as SHOK
  end.

Ltac hprune := try (match goal with
  | Z0 : dsh_cell ?p ?N ?y = 0, NZ : 0 < dsh_cell ?p ?N ?x |- _ =>
    exfalso; apply (hd_cell_mono p N x y ltac:(assumption) ltac:(unfold d_cur; lia) ltac:(lia)); exact Z0 end).

Ltac hconv cx n :=
  lazymatch goal with
  | Hc : branch_taken BC_EQ (sv_denot ?Ex (SExt true 8 (SOff ?v 0))) (sv_denot ?Ex (SLit 0)) = ?bb |- _ =>
    let s := hval Ex v in
    lazymatch s with dsh_cell ?a ?b ?c => pose proof (dsh_cell_range a b c) end;
    rewrite (hd_beq_cell Ex v s ltac:(hew; reflexivity) ltac:(lia)) in Hc;
    lazymatch bb with
    | true => apply Z.eqb_eq in Hc; let H := fresh "HZ" in rename Hc into H; hprune
    | false => apply Z.eqb_neq in Hc; let H := fresh "HNZ" in assert (H : 0 < s) by lia; clear Hc
    end
  | Hc : branch_taken BC_GE (sv_denot ?Ex (SAlu ALU_AND (SOff 531 ?c) (SLit 7))) (sv_denot ?Ex (SExt true 8 (SOff ?v 0))) = ?bb |- _ =>
    let s := hval Ex v in
    lazymatch s with dsh_cell ?a ?b ?x => pose proof (dsh_cell_range a b x) end;
    rewrite (hd_bge_cell Ex 531 c (d_cur cx n) v s ltac:(hew; reflexivity) ltac:(unfold d_cur; lia) ltac:(lia)
      ltac:(unfold d_cur; lia) ltac:(hew; reflexivity) ltac:(lia)) in Hc;
    lazymatch bb with
    | true => exfalso; apply negb_true_iff in Hc; apply Z.ltb_ge in Hc;
        lazymatch goal with NZ : 0 < s |- _ =>
          pose proof (dsh_cell_lt (c_p cx) (c_n cx) (d_cur cx n + c) ltac:(assumption) ltac:(lia) ltac:(unfold d_cur; lia) ltac:(lia)); lia end
    | false => clear Hc
    end
  end.

Ltac hsv cx n now dt :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => reflexivity
  | |- sv_denot _ (SOff 516 _) = _ => cbn [sv_denot]; hew; hrewU; unfold w64, d_obj, dobj_off; reflexivity
  | |- sv_denot _ (SOff ?q 0) = _ => rewrite sv_denot_SOff0; hew; first [ reflexivity | assumption ]
  | |- sv_denot _ (SOff ?q ?c) = _ => rewrite denot_lit_U; unfold w64; f_equal; rewrite U_SOff; hew; unfold w64;
      rewrite unsigned_lit_small by (unfold d_cur; lia); unfold d_cur; rewrite zcanon_id by (unfold M64; lia); lia
  | |- sv_denot ?Ex (SExt true 8 (SOff 551 0)) = _ =>
      rewrite denot_lit_U, (hd_U_sext8 Ex 551 (hb cx n 0)) by (first [ hew; reflexivity | apply hb_range ]);
      apply hd_w64_sext; apply hb_range
  | |- sv_denot ?Ex (SMd M_MUL ?X (SLit 1000000)) = _ =>
      rewrite denot_lit_U; unfold w64; f_equal; apply (hd_U_mul Ex X dt);
      [ first [ apply (hd_U_dt1 Ex 552 (hb cx n 1)); [hew; reflexivity | apply hb_range]
              | apply (hd_U_dt2 Ex 553 552 (hb cx n 2) (hb cx n 1)); [hew; reflexivity | apply hb_range | hew; reflexivity | apply hb_range]
              | rewrite U_SLit; reflexivity
              | rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SLit; reflexivity ]
      | pose proof (hb_range cx n 1); pose proof (hb_range cx n 2); lia ]
  end.

Ltac hreg cx n now dt :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms) |- _ =>
    lazymatch goal with
    | |- YG0d.spZ _ = _ =>
      unfold YG0d.spZ;
      let R := fresh "R" in pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms 2%bv HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in change (sr_get (ss_regs ss) 2%bv) with e in R;
      rewrite R, sv_denot_SOff0; hew; first [ assumption | hrewU; reflexivity ]
    | |- getr _ ?r = _ =>
      let R := fresh "R" in pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
      rewrite R; clear R; hsv cx n now dt
    end
  end.

Ltac hdE := lazymatch goal with HE : d_E ?cx ?E |- d_E ?cx ?Ec =>
  apply (hd_d_E_agree cx E Ec HE); let k0 := fresh "k0" in let Hk0 := fresh "Hk0" in intros k0 Hk0;
  repeat (rewrite ew_havoc_old by (unfold AT_FL; lia)); unfold d_env; apply ew_havoc_old; unfold AT_FL; lia end.

Ltac hland_mid cx h i n now n' dt fq ly3 S3 W mem3 acc :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H _) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md ?k |- _ =>
    apply SRr_ret; exists n', now, (hb cx n 0), dt;
    eapply hd_d_at_mono;
    [ apply (hdr_land_mid fq cx h i n now ly3 S3 W mem3 md k acc Ec ss ms n'
        MID_OFF (d_rM B cx i n' now (hb cx n 0) dt)
        (0 <= i < MAX_OPS /\ 0 <= n' /\ 0 <= now < 2 ^ 64 /\ 0 <= hb cx n 0 < 256 /\ 0 <= dt < 65536));
      [ assumption | assumption | exact HJ | assumption | assumption | assumption | assumption | assumption | hdE | hew; reflexivity
      | exact HS | reflexivity | reflexivity | vm_compute; reflexivity | assumption | assumption | assumption | lia
      | unfold d_rM, d_rL; repeat split; hreg cx n now dt
      | split; [lia|]; split; [lia|]; split; [lia|]; split; [apply hb_range | pose proof (hb_range cx n 1); pose proof (hb_range cx n 2); lia] ]
    | let regs := fresh "regs" in let ly := fresh "ly" in let S := fresh "S" in let W' := fresh "W" in
      let mem := fresh "mem" in let md := fresh "md" in let Q := fresh "Q" in let P := fresh "P" in let BD := fresh "BD" in
      intros regs ly S W' mem md (Q & P & BD); destruct Q as (Q1 & Q2 & Q3 & Q4 & Q5);
      exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj P BD)))))) ]
  end.

Ltac hgo RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc stop :=
  hrun RUNTO stop; hdisp RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc stop
with hdisp RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 2256 => hland_mid cx h i n now n' dt fq ly3 S3 W mem3 acc
    | 2120 => hcell 0 (10%bv : bv 5) 560%nat 561%nat cx n; hgo RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc 2168
    | 2168 => hcell 1 (10%bv : bv 5) 562%nat 563%nat cx n; hgo RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc 2216
    | 2216 => hcell 2 (12%bv : bv 5) 564%nat 565%nat cx n; hgo RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc 2256
    | _ =>
      lazymatch goal with HS' : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
        psrr_branch_tok RUN BR HS' SHOK Bspan;
        [ hconv cx n; hgo RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc stop
        | hconv cx n; hgo RUNTO RUN BR cx h i n now n' dt fq ly3 S3 W mem3 acc stop ]
      end
    end
  end.

Ltac hprep cx h i n now regs ly3 S3 W mem3 md3 k :=
  lazymatch goal with HB : d_base _ _ _ _ _ _ cx, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFR : frames S3 = _, HR : d_rH _ cx h i n now regs, HBD : d_body _ cx h n [] dsh_loop ly3 S3 W mem3 |- _ =>
  pose proof HB as ((HPRE & Hra & Hp & Hn0 & Hpn & Hlen & Hgarr0 & _) & _);
  pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk & _);
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _);
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR; unfold YG0f.ASAN_CEIL in CR;
  pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOI & HGEO & HCAN & HAWR);
  pose proof HFRM as (E & HE & HRG & HFL & H216 & H152);
  pose proof HINP as (Hnr & HG & HOIp);
  pose proof HE as (EE & E32 & HEI0 & E60 & E516 & E529); unfold AT_A, AT_F, AT_SH in E60, E516, E529;
  pose proof HBLK as (Hperm & _ & _ & _);
  assert (HN8 : 8 <= c_n cx) by lia;
  assert (HinB0 : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))) by (destruct Hpn as [[? _]|[_ ?]]; [lia | assumption]);
  assert (HN26 : c_n cx < 2 ^ 26) by (destruct Hpn as [[? _]|[? _]]; lia);
  assert (HinB : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by
    (apply (Permutation_in _ (Permutation_sym Hperm)); cbn [app]; right; exact HinB0);
  pose proof HJ as (HAR3 & HLY & _);
  assert (HinH : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm)); cbn [app]; left; reflexivity);
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinH) as (_ & Hh4k & Hhc & _ & _);
  change (req_size HUNT_SIZE) with 480 in Hhc;
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY) as (_ & EFA3 & _);
  assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity);
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 Hfin) as (HF0 & HFc & HFapp);
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 HinB Hfin) as HBF;
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinB) as (Hp16 & Hp4k & Hpc & Hpapp & _);
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hfin) as (HF32 & _);
  rewrite EFA3 in HF0, HFc, HFapp, HBF, HF32; fold (d_FB cx) in HF0, HFc, HFapp, HBF, HF32;
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia);
  rewrite Hrq in Hpc, Hpapp, HBF;
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in HF0, HFc, HFapp, HBF;
  assert (Hp8 : c_p cx mod 8 = 0) by (pose proof (Z.div_mod (c_p cx) 16 ltac:(lia)); pose proof (Z.div_mod (c_p cx) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (c_p cx) 8 ltac:(lia)); lia);
  assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia);
  destruct (hd_A_range cx HS608) as [HAr _];
  assert (HSr : 0 <= d_S cx <= 2 ^ 47) by (unfold d_S, LLVMF_STK in *; lia);
  assert (HSlo : alloc_ceiling + 32768 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia);
  pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Ho1; pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Ho66;
  pose proof (pa_val_range (A_OBJ 1)) as RV1; pose proof (pa_val_range (A_OBJ 66)) as RV66;
  assert (EO1 : ew E 242 = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E 242 HEI0); unfold A_TEXT, A_LIM; lia);
  assert (EO66 : ew E 307 = Z_to_bv 64 (VAL (A_OBJ 66))) by (apply (img_env_atomP E 307 HEI0); unfold A_TEXT, A_LIM; lia);
  assert (E2 : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, YG0d.spZ; symmetry; apply Z_to_bv_bv_unsigned);
  assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0);
  assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp0);
  assert (UA : bv_unsigned (ew E 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; unfold d_S, LLVMF_STK in *; lia);
  assert (US : bv_unsigned (ew E 2) = d_S cx) by (rewrite E2; apply unsigned_lit_small; unfold d_S, LLVMF_STK in *; lia);
  assert (UF : bv_unsigned (ew E 516) = d_FB cx) by (rewrite E516; apply unsigned_lit_small; lia);
  assert (USH : bv_unsigned (ew E 529) = shadow_addr (d_FB cx)) by
    (rewrite E529; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF;
     pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia)); pose proof (Z.div_le_upper_bound (d_FB cx) 8 (d_FB cx) ltac:(lia) ltac:(lia)); lia);
  assert (UO1 : bv_unsigned (ew E 242) = VAL (A_OBJ 1)) by (rewrite EO1; apply unsigned_lit_small; lia);
  assert (UO66 : bv_unsigned (ew E 307) = VAL (A_OBJ 66)) by (rewrite EO66; apply unsigned_lit_small; lia);
  assert (Hn7 : 0 <= n <= c_n cx - 7) by lia; clear Hnr Hpn Hp16;
  match goal with Hi0 : 0 <= i < MAX_OPS |- _ => assert (HiR : 0 <= i < 2 ^ 64) by (unfold MAX_OPS in Hi0; lia) end
  end.

Lemma hdr_c1 : forall (fq : YK11.FPState) cx h i ly3 S3 (W : world SEGS) (regs : bvmap 5 word) mem3 md3 k acc n now,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  0 <= i < MAX_OPS -> n = 1 -> 0 <= now < 2 ^ 64 -> d_rH B cx h i n now regs ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + HDR_OFF) regs mem3 md3) (hdr_mid B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i ly3 S3 W regs mem3 md3 k acc n now HB HFQ HJ HFR Hk Hev Hmo Hacc Hi Hn1 Hnow HR HBD.
hprep cx h i n now regs ly3 S3 W mem3 md3 k.
pose proof HR as (_ & _ & _ & H7' & _).
pose proof (hdr_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx h i n now ly3 S3 W regs mem3 md3 k E (SLit 1) 1%nat false
  (conj HB (conj HJ HFR)) HE HRG HFL HR
  ltac:(rewrite H7'; first [ subst n; reflexivity | rewrite sv_denot_SOff0; hew; reflexivity ])
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(first [ intros Hf; discriminate Hf | intros _; lia ])
  ltac:(lia) Hnow ltac:(lia) HinB ltac:(lia) HN26 HG ltac:(apply HOIp; lia)) as HS.
unfold cfg_at; change (w64 (BASE + HDR_OFF)) with (Z_to_bv 64 (BASE + HDR_OFF)).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO; pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (HEI : img_env VAL A_LIM (d_env cx E (hdr_vals cx h i n now regs))) by
  (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (Forall_nil (shent_ok SEGS (SOff 32 0) (d_env cx E (hdr_vals cx h i n now regs)) (mrestrict (w_H W) mem3)) :
  sh_ok SEGS (SOff 32 0) [] (d_env cx E (hdr_vals cx h i n now regs)) (mrestrict (w_H W) mem3)) as SHOK.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 232 <= a < d_A cx + 352) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a)
  by reflexivity.
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by auto.
unfold hdr_ss in HS; norm_ss HS.
hgo RUNTO RUN BR cx h i n now 0 0 fq ly3 S3 W mem3 acc 2120.
Qed.
Lemma hdr_c2 : forall (fq : YK11.FPState) cx h i ly3 S3 (W : world SEGS) (regs : bvmap 5 word) mem3 md3 k acc n now,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  0 <= i < MAX_OPS -> n = 2 -> 0 <= now < 2 ^ 64 -> d_rH B cx h i n now regs ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + HDR_OFF) regs mem3 md3) (hdr_mid B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i ly3 S3 W regs mem3 md3 k acc n now HB HFQ HJ HFR Hk Hev Hmo Hacc Hi Hn1 Hnow HR HBD.
hprep cx h i n now regs ly3 S3 W mem3 md3 k.
pose proof HR as (_ & _ & _ & H7' & _).
pose proof (hdr_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx h i n now ly3 S3 W regs mem3 md3 k E (SLit 2) 2%nat false
  (conj HB (conj HJ HFR)) HE HRG HFL HR
  ltac:(rewrite H7'; first [ subst n; reflexivity | rewrite sv_denot_SOff0; hew; reflexivity ])
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(first [ intros Hf; discriminate Hf | intros _; lia ])
  ltac:(lia) Hnow ltac:(lia) HinB ltac:(lia) HN26 HG ltac:(apply HOIp; lia)) as HS.
unfold cfg_at; change (w64 (BASE + HDR_OFF)) with (Z_to_bv 64 (BASE + HDR_OFF)).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO; pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (HEI : img_env VAL A_LIM (d_env cx E (hdr_vals cx h i n now regs))) by
  (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (Forall_nil (shent_ok SEGS (SOff 32 0) (d_env cx E (hdr_vals cx h i n now regs)) (mrestrict (w_H W) mem3)) :
  sh_ok SEGS (SOff 32 0) [] (d_env cx E (hdr_vals cx h i n now regs)) (mrestrict (w_H W) mem3)) as SHOK.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 232 <= a < d_A cx + 352) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a)
  by reflexivity.
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by auto.
unfold hdr_ss in HS; norm_ss HS.
hgo RUNTO RUN BR cx h i n now 0 (hb cx n 1) fq ly3 S3 W mem3 acc 2120.
Qed.
Lemma hdr_c3 : forall (fq : YK11.FPState) cx h i ly3 S3 (W : world SEGS) (regs : bvmap 5 word) mem3 md3 k acc n now,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  0 <= i < MAX_OPS -> 3 <= n -> 0 <= now < 2 ^ 64 -> d_rH B cx h i n now regs ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + HDR_OFF) regs mem3 md3) (hdr_mid B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i ly3 S3 W regs mem3 md3 k acc n now HB HFQ HJ HFR Hk Hev Hmo Hacc Hi Hn1 Hnow HR HBD.
hprep cx h i n now regs ly3 S3 W mem3 md3 k.
pose proof HR as (_ & _ & _ & H7' & _).
pose proof (hdr_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx h i n now ly3 S3 W regs mem3 md3 k E (SOff 532 0) 3%nat true
  (conj HB (conj HJ HFR)) HE HRG HFL HR
  ltac:(rewrite H7'; first [ subst n; reflexivity | rewrite sv_denot_SOff0; hew; reflexivity ])
  ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(first [ intros Hf; discriminate Hf | intros _; lia ])
  ltac:(lia) Hnow ltac:(lia) HinB ltac:(lia) HN26 HG ltac:(apply HOIp; lia)) as HS.
unfold cfg_at; change (w64 (BASE + HDR_OFF)) with (Z_to_bv 64 (BASE + HDR_OFF)).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO; pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (HEI : img_env VAL A_LIM (d_env cx E (hdr_vals cx h i n now regs))) by
  (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (Forall_nil (shent_ok SEGS (SOff 32 0) (d_env cx E (hdr_vals cx h i n now regs)) (mrestrict (w_H W) mem3)) :
  sh_ok SEGS (SOff 32 0) [] (d_env cx E (hdr_vals cx h i n now regs)) (mrestrict (w_H W) mem3)) as SHOK.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 232 <= a < d_A cx + 352) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a)
  by reflexivity.
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by auto.
unfold hdr_ss in HS; norm_ss HS.
hgo RUNTO RUN BR cx h i n now (n - 3) (hb cx n 2 * 256 + hb cx n 1) fq ly3 S3 W mem3 acc 2120.
Qed.

Theorem hdr_s1 : hdr_seg1 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & HB & HJ & HFR & Hk & Hev & Hmo & Hacc & n & now & Hi & Hn & Hnow & HR & HBD).
assert (Hc : n = 1 \/ n = 2 \/ 3 <= n) by lia.
destruct Hc as [Hc | [Hc | Hc]].
- exact (hdr_c1 fq cx h i ly3 S3 W regs mem3 md3 k acc n now HB HFQ HJ HFR Hk Hev Hmo Hacc Hi Hc Hnow HR HBD).
- exact (hdr_c2 fq cx h i ly3 S3 W regs mem3 md3 k acc n now HB HFQ HJ HFR Hk Hev Hmo Hacc Hi Hc Hnow HR HBD).
- exact (hdr_c3 fq cx h i ly3 S3 W regs mem3 md3 k acc n now HB HFQ HJ HFR Hk Hev Hmo Hacc Hi Hc Hnow HR HBD).
Qed.
End h.
End f.
End d.
