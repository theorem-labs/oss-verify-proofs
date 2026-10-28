(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5KnA_u PnSrcSMemmove_u PnIssStmts_u PnIssSP_u
     Bs0_code_r342cc_342d0_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMIS3.
Import PMS.

Lemma csk_icCl1a : forall k, In k PMIS.CSK -> In k PMISP.KS_icCl1a. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icCl1b : forall k, In k PMIS.CSK -> In k PMISP.KS_icCl1b. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icCl2 : forall k, In k PMIS.CSK -> In k PMISP.KS_icCl2. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icCl3 : forall k, In k PMIS.CSK -> In k PMISP.KS_icCl3. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icCl4 : forall k, In k PMIS.CSK -> In k PMISP.KS_icCl4. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_CS : forall k, In k PMIS.CSK -> In k L5K.CS. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_cs : forall k, In k PMIS.CSK -> In k PMK.cs_all. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.

Ltac t14 AG C := lazymatch type of C with
  | L5.u64_at _ ?Ms _ _ => apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.u32_at _ ?Ms _ _ => apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.u8_at _ ?Ms _ _ => apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.defined ?Ms _ _ => apply (L5C.defined_agree Ms); [intros i Hi; apply AG; lia | first [exact C | PMK.gmem]]
  | L5KA.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
                               apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  | PM.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
                            apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  end.
Ltac gx AG :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M2 ?a ?v => match goal with H : L5.u64_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  | |- L5.u32_at ?sg ?M2 ?a ?v => match goal with H : L5.u32_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  | |- L5.u8_at ?sg ?M2 ?a ?v => match goal with H : L5.u8_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (L5C.u8_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  end.

(* [comment removed for export] *)
Definition cap_of (n : Z) : Z := if Z.leb n 44 then 48 else 8 * (n / 8) + 8.
Lemma cap_facts n : 23 <= n < 2 ^ 26 -> n < cap_of n /\ cap_of n <= n + 32 /\ cap_of n mod 8 = 0 /\ 48 <= cap_of n <= 2 ^ 26 + 8.
Proof.
  intros Hn. unfold cap_of. destruct (Z.leb_spec n 44) as [LE|GT]; [cbn; Lia.lia|].
  pose proof (Z.div_mod n 8 ltac:(Lia.lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(Lia.lia)) as B.
  split; [Lia.lia|]. split; [Lia.lia|]. split; [|Lia.lia].
  replace (8 * (n / 8) + 8) with ((n / 8 + 1) * 8) by Lia.lia. apply Z.mod_mul. Lia.lia.
Qed.

(* [comment removed for export] *)
Definition hl_ok (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (ois os sp n p : Z) (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) : Prop :=
  mem_grows M M2
  /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 192 <= i < sp - 192 + 48) -> ~ (ois + 16 <= i < ois + 16 + 8) -> ~ (ois + 32 <= i < ois + 32 + 84) ->
        M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
  /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36204) M (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0xb03b8) M2 (seg_rom RSEGS))
  /\ (forall k, In k PMIS.CSK -> getr R2 (PMK.reg k) = getr R (PMK.reg k))
  /\ getr R2 (PMK.reg 1) = Z_to_bv 64 364116 /\ getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 192)
  /\ getr R2 (PMK.reg 8) = Z_to_bv 64 n /\ getr R2 (PMK.reg 9) = Z_to_bv 64 (ois + 80) /\ getr R2 (PMK.reg 10) = Z_to_bv 64 (cap_of n)
  /\ getr R2 (PMK.reg 18) = Z_to_bv 64 (ois + 80) /\ getr R2 (PMK.reg 19) = Z_to_bv 64 p /\ getr R2 (PMK.reg 20) = Z_to_bv 64 (cap_of n - 1)
  /\ L5.u64_at RSEGS M2 (sp - 192) os /\ L5.u64_at RSEGS M2 (sp - 184) 8 /\ L5.u64_at RSEGS M2 (sp - 176) (ois + 80)
  /\ L5.u64_at RSEGS M2 (sp - 168) (ois + 24) /\ L5.u64_at RSEGS M2 (sp - 160) (ois + 16) /\ L5.u64_at RSEGS M2 (sp - 152) 221768
  /\ L5.u32_at RSEGS M2 (ois + 112) 8 /\ L5.u64_at RSEGS M2 (ois + 16) 740552 /\ PM.zeros_at M2 (ois + 32) 48.

Lemma head_long fx R M ois os sp n p c :
  getr R (PMK.reg 2) = Z_to_bv 64 (sp - 144) -> getr R (PMK.reg 8) = Z_to_bv 64 (ois + 16) -> getr R (PMK.reg 9) = Z_to_bv 64 (ois + 24) ->
  getr R (PMK.reg 19) = Z_to_bv 64 8 -> getr R (PMK.reg 20) = Z_to_bv 64 os -> getr R (PMK.reg 21) = Z_to_bv 64 740424 ->
  140735332503552 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> sp <= ois -> ois + 272 <= os -> os + 24 <= 2 ^ 47 -> os - ois <= 8388608 -> ois mod 8 = 0 -> os mod 8 = 0 ->
  L5.writable RSEGS M (sp - 208) 208 -> L5.writable RSEGS M ois 272 -> L5.img_clear M 65536 754672 ->
  L5.u8_at RSEGS M os ((c + 1) mod 256) -> c mod 2 = 0 -> 0 <= c ->
  L5.u64_at RSEGS M (os + 8) n -> L5.u64_at RSEGS M (os + 16) p -> 0 <= p < 2 ^ 64 -> 23 <= n < 2 ^ 26 ->
  exists fx2 R2 M2, hl_ok fx R M ois os sp n p fx2 R2 M2.
Proof.
  intros R2 R8 R9 R19 R20 R21 Hsp S16 Hspo Hoos Hostop Hd Ho8 Hos8 WR0 WRO RO U0 Hc Hc0 N8 P16 Hp Hn.
  pose proof (PMF.odd_byte c Hc Hc0) as ODD.
  destruct (Z_le_gt_dec n 44) as [LE|GT].
  - LeanFeed.pfeed P (PMISP.icCl1a_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => ois | 36%nat => p | 38%nat => (c + 1) mod 256 | 39%nat => os - ois
                                                            | 40%nat => n | _ => 0 end)) ltac:(first [ PMK.sc | exact RO | exact ODD | (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia) ]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx2 & R3 & M2 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG & FR & FRZ & MS & KS & B1 & B2 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B18 & B19 & B20
                        & S192 & S184 & S176 & S168 & S160 & S152 & C112 & C104 & C96 & C88 & C80 & C16 & Z32)); PMK.pvz_clrT.
    exists fx2, R3, M2. unfold hl_ok. assert (E : cap_of n = 48) by (unfold cap_of; destruct (Z.leb_spec n 44); lia). rewrite E.
    split; [exact MG|]. split; [exact FRZ|]. split; [exact MS|]. split; [intros k Hk; apply KS; apply csk_icCl1a; exact Hk|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B18|]. split; [exact B19|].
    split; [exact B20|]. split; [PMK.gmem|]. repeat (split; [PMK.gmem|]). exact Z32.
  - assert (L7 : Z.lor n 7 = 8 * (n / 8) + 7) by (pose proof (PMF.lor7 n ltac:(lia)); lia).
    pose proof (Z.div_mod n 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MB.
    LeanFeed.pfeed P (PMISP.icCl1b_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => ois | 36%nat => p | 38%nat => (c + 1) mod 256 | 39%nat => os - ois
                                                            | 40%nat => n | _ => 0 end)) ltac:(first [ PMK.sc | exact RO | exact ODD | (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia) | (rewrite L7; lia) ]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx2 & R3 & M2 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG & FR & FRZ & MS & KS & B1 & B2 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B18 & B19 & B20
                        & S192 & S184 & S176 & S168 & S160 & S152 & C112 & C104 & C96 & C88 & C80 & C16 & Z32)); PMK.pvz_clrT.
    exists fx2, R3, M2. unfold hl_ok. assert (E : cap_of n = 8 * (n / 8) + 8) by (unfold cap_of; destruct (Z.leb_spec n 44); lia). rewrite E.
    split; [exact MG|]. split; [exact FRZ|]. split; [exact MS|]. split; [intros k Hk; apply KS; apply csk_icCl1b; exact Hk|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B8|]. split; [exact B9|]. split; [exact B10|]. split; [exact B18|]. split; [exact B19|].
    split; [replace (8 * (n / 8) + 8 - 1) with (8 * (n / 8) + 7) by lia; exact B20|]. split; [PMK.gmem|]. repeat (split; [PMK.gmem|]). exact Z32.
Qed.

Lemma outside_WF_ois ois b a : L5.outside (PMIS.WF ois b) a -> L5.outside [(ois, 272)] a.
Proof.
  intros O. unfold PMIS.WF in O. apply L5C.outside_cons_inv in O. apply L5C.outside_cons; [exact (proj1 O)| apply L5C.outside_nil].
Qed.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma defined_dk LB sp scr M M' a n : PMK.dk L LB sp scr M M' -> L5C.stk (hl_sptop L) M sp scr -> 0 <= scr -> sp <= a -> a + n <= 2 ^ 64 ->
  L5.defined M a n -> L5.defined M' a n.
Proof.
  intros DK (S16 & SB & SC & SD & SW) S0 Ha Hn D i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
  apply DK; [lia| | unfold in_errno; lia| apply D; exact Hi]. right. left. unfold hl_ceil. split; lia.
Qed.

Lemma tail_long : PMS.opnew_spec L HI ->
  forall (fx1 : FPState) R0 M0 model0 K LB cr ois os sp r s b R1 M1 model1 c n p,
    PMIS.pre L HI R0 M0 model0 K LB cr ois os sp r s b ->
    PMIS.kont L HI R0 M0 model0 K LB cr ois sp r s b ->
    s = PM.VLong c n p ->
    PMIS.mid L HI R0 M0 model0 LB cr ois os sp s b R1 M1 model1 ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36204 M1 model1) K.
Proof.
  intros OPNEW fx1 R0 M0 model0 K LB cr ois os sp r s b R1 M1 model1 c n p PRE KONT Es MID.
  destruct PRE as (_ & _ & K0 & ENT & _ & _ & _ & Hspo & Hoos & Hostop & Ho8 & Hos8 & _ & _ & INCL & SZ & LNG & _ & _ & CRED).
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & _ & Rtp & STK0).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. cbn [pa_tp AD PnLayoutS_u.ADDR_S] in Rtp.
  destruct MID as (R2 & R8 & R9 & R19 & R20 & R21 & RCSK & SI & SB & HC & DEF1 & VS1 & STK1 & BASE1 & LOC1 & HH1 & MOK1 & MB1 & EK01 & DK01).
  pose proof MOK1 as (Mh & Ml & Mm).
  pose proof (L5C.stk_floor _ _ _ _ STK1) as FL. pose proof (L5C.stk_writable RSEGS _ M1 sp _ STK1) as WR1.
  pose proof STK1 as (S16 & SBd & SC & SD & SW). unfold PMIS.SCR in *.
  assert (CEIL : hl_ceil L <= sp - 20480) by (unfold hl_ceil; lia).
  assert (WRO : L5.writable RSEGS M1 ois 272) by (apply (L5C.writable_of_defined RSEGS M1 ois 272 DEF1); lia).
  pose proof (PMCK.lb_hi L HI HIok LB cr M1 _ HH1) as LBhi.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M1 _ HH1 (incl_refl _))).
  pose proof BASE1 as (RO1 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO1.
  subst s. cbn [PM.vs_size PM.vs_own] in SZ, CRED, INCL. unfold PMIS.cost in CRED. cbn [PM.vs_size] in CRED.
  specialize (LNG c n p eq_refl).
  destruct VS1 as (DEFS & _ & W0 & N8 & P16 & Hnc & Hc & Hc2 & DEFP & _).
  assert (INs : In (p, c) LB) by (apply INCL; left; reflexivity).
  destruct (BR p c INs) as (Bp0 & Bp1 & Bp2).
  pose proof (cap_facts n ltac:(lia)) as (CF1 & CF2 & CF3 & CF4). set (cap := cap_of n) in *.
  pose proof (PMF.u8_of_u64 RSEGS M1 os (c + 1) ltac:(lia) W0) as U0.
  (* [comment removed for export] *)
  destruct (head_long fx1 R1 M1 ois os sp n p c R2 R8 R9 R19 R20 R21 ltac:(lia) S16 Hspo Hoos ltac:(lia) ltac:(lia) Ho8 Hos8
              ltac:(apply (L5.writable_sub RSEGS M1 (sp - 20480) 20480); [exact WR1|lia|lia]) WRO RO1 U0 ltac:(Lia.lia) ltac:(lia) N8 P16 ltac:(lia) ltac:(lia))
    as (fx2 & R3 & M2 & MG2 & FRZ2 & MS2 & KS2 & B1 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & S192 & S184 & S176 & S168 & S160 & S152 & C112 & C16 & Z32).
  fold cap in B10, B20.
  unfold PMSP.cfg.
  set (P2 := fun a => sp - 192 <= a < sp - 144 \/ ois + 16 <= a < ois + 24 \/ ois + 32 <= a < ois + 116).
  assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P2 in NP. apply FRZ2; [exact Ha| | |]; intros X; apply NP; lia. }
  assert (CW2 : forall a, P2 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M1 sp 20480 a STK1). unfold P2 in Ha. lia. }
  assert (DEC2 : forall a, {P2 a} + {~ P2 a}) by (intros a; unfold P2; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model1 fx1 fx2 R1 0x36204 R3 0xb03b8 M2 P2 K HH1 Mh Ml ltac:(lia) MS2 MG2 AG2 CW2 DEC2).
  intros HH2.
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (L5C.stk_grows _ M1 M2 _ _ MG2 STK1)).
  assert (EK12 : PMK.ek L LB sp 20480 [(ois, 272)] M1 M2).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M1 M2 P2 AG2 STK1 LBhi). intros a X. unfold P2 in X.
    destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
  (* [comment removed for export] *)
  assert (SCn : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
  assert (STKn : L5C.stk (hl_sptop L) M2 (sp - 192) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M2 sp 20480 (sp - 192) PMSP.OPNEW_SCR STK2); unfold PMSP.OPNEW_SCR; lia. }
  unfold PMS.opnew_spec, PMSP.opnew_spec in OPNEW. cbn [pa_opnew pa_tp AD PnLayoutS_u.ADDR_S] in OPNEW.
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
  apply (OPNEW fx2 R3 M2 model1 K LB cr cap (sp - 192) 364116 HH2 MOK1 K0).
  { rewrite L5K.rl10. exact B10. } { lia. }
  { destruct CRED as (CR1 & CR2). unfold PM.cost1 in CR1, CR2. cbn [fst snd] in CR1, CR2. unfold credit_ok. lia. }
  { rewrite L5K.rl1. exact B1. } { split; [lia| reflexivity]. } { rewrite L5K.rl2. exact B2. }
  { rewrite L5K.rl4. rewrite (KS2 4%nat) by PMK.inl. rewrite (RCSK 4%nat) by PMK.inl. exact Rtp. } { exact STKn. }
  intros fx3 R4 M3 model3 B A10b RP3 FRESH HP3 MB3 HH3. rewrite L5K.rl10 in A10b.
  destruct (L5C.fresh_block_bounds L LB M3 B cap FRESH) as (FB0 & FBH & FB16 & _ & FBC).
  destruct FRESH as (_ & FAP & FDEF).
  pose proof (PMFR.model_ok_but_vm model1 model3 MOK1 MB3) as MOK3. pose proof MOK3 as (Mh3 & Ml3 & Mm3).
  assert (AG3 : forall a, sp - 192 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha. apply (L5C.hpres_kept L LB (sp - 192) PMSP.OPNEW_SCR [] M2 M3 a HP3).
    apply (PMKP.kept_stack RSEGS L KL LB M2 (sp - 192) PMSP.OPNEW_SCR [] a STKn SCn Ha). apply L5C.outside_nil. }
  assert (AGp : L5C.agree_on M2 M3 p c).
  { apply (PMFR.ag_block RSEGS L KL LB (sp - 192) PMSP.OPNEW_SCR [] M2 M3 (PMK.ek_of_hpres L LB _ _ _ M2 M3 HP3) STKn SCn BR); [| exact INs].
    intros a X. destruct (PMFR.inW_nil a X). }
  assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480).
  { apply (PMK.stk_after RSEGS L KL LB M2 M3 sp 20480 (sp - 192) PMSP.OPNEW_SCR [] STK2 HP3); unfold PMSP.OPNEW_SCR; lia. }
  assert (EK23 : PMK.ek L LB sp 20480 [(ois, 272)] M2 M3).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB sp 20480 (sp - 192) PMSP.OPNEW_SCR [(ois, 272)] [] M2 M2 M3 HP3 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia| exact STK2| exact LBhi|].
    intros a X. destruct (PMFR.inW_nil a X). }
  assert (DK23 : PMK.dk L LB sp 20480 M2 M3).
  { apply (PMK.dk_callee L LB LB sp 20480 (sp - 192) PMSP.OPNEW_SCR [] M2 M3 HP3 (incl_refl _)); unfold PMSP.OPNEW_SCR; lia. }
  set (LB3 := (B, cap) :: LB) in *.
  (* [comment removed for export] *)
  assert (R4sp : getr R4 (PMK.reg 2) = Z_to_bv 64 (sp - 192)) by (rewrite (PMK.cs_of_preserved R3 R4 2 RP3 ltac:(PMK.inl)); exact B2).
  assert (R4s0 : getr R4 (PMK.reg 8) = Z_to_bv 64 n) by (rewrite (PMK.cs_of_preserved R3 R4 8 RP3 ltac:(PMK.inl)); exact B8).
  assert (R4s3 : getr R4 (PMK.reg 19) = Z_to_bv 64 p) by (rewrite (PMK.cs_of_preserved R3 R4 19 RP3 ltac:(PMK.inl)); exact B19).
  LeanFeed.pfeed P (PMISP.icCl2_conc fx3 R4 M3 (fun j => match j with 2%nat => sp | 36%nat => p | 40%nat => n | 41%nat => B | _ => 0 end)) ltac:(first [ PMK.sc ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx4 & R5 & M4 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG4 & FR4 & FRZ4 & MS4 & KS4 & F1 & F11 & F12 & F18)); PMK.pvz_clrT.
  clear FR4.
  apply (PMK.spiece RSEGS L HI KL HIok LB3 (debit L cr cap) M3 model3 fx3 fx4 R4 0x58e54 R5 0xab480 M4 (fun _ => False) K HH3 Mh3 Ml3 ltac:(lia) MS4 MG4);
    [intros a Ha _; apply FRZ4; exact Ha| intros a []| intros a; right; intros []|].
  intros HH4.
  (* [comment removed for export] *)
  assert (DEFp4 : L5.defined M4 p n).
  { apply (L5C.defined_agree M3 M4); [intros i Hi; apply FRZ4; lia|]. apply (L5C.defined_agree M2 M3); [apply (L5C.agree_on_sub M2 M3 p c); [exact AGp|lia|lia]|].
    apply (L5C.defined_agree M1 M2); [intros i Hi; apply AG2; [lia| unfold P2; lia]|]. apply (L5.defined_sub M1 p c); [exact DEFP|lia|lia]. }
  assert (WRB4 : L5.writable RSEGS M4 B cap).
  { apply (L5C.writable_of_defined RSEGS M4 B cap); [|lia|lia]. apply (L5C.defined_agree M3 M4); [intros i Hi; apply FRZ4; lia| exact FDEF]. }
  assert (APc : B + n <= p \/ p + n <= B) by (destruct (L5C.blocks_apart_in B cap LB p c FAP INs); lia).
  destruct (PMCPS.memcpy_run fx4 R5 M4 B p n 364132) as (R6 & M5 & MS5 & MG5 & FR5 & DEF5 & KS5 & G10);
    [ rewrite (KS4 10%nat) by PMK.inl; exact A10b | exact F11 | exact F12 | exact F1 | split; [lia| reflexivity] | lia | lia | lia | lia | lia | exact APc
    | apply (L5.writable_sub RSEGS M4 B cap); [exact WRB4|lia|lia] | exact DEFp4 | ].
  set (P5 := fun a => B <= a < B + cap).
  assert (AG5 : forall a, 0 <= a < 2 ^ 64 -> ~ P5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by (intros a Ha NP; unfold P5 in NP; apply FR5; [exact Ha| lia]).
  assert (CW5 : forall a, P5 a -> PMK.cwr L LB3 a) by (intros a Ha; apply (PMK.cwr_block L LB3 B cap a); [left; reflexivity| exact Ha]).
  assert (DEC5 : forall a, {P5 a} + {~ P5 a}) by (intros a; unfold P5; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB3 (debit L cr cap) M4 model3 fx4 fx4 R5 0xab480 R6 364132 M5 P5 K HH4 Mh3 Ml3 ltac:(lia) MS5 MG5 AG5 CW5 DEC5).
  intros HH5.
  (* [comment removed for export] *)
  assert (AG25 : forall a, sp - 192 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha. rewrite (AG5 a) by (unfold P5; lia). rewrite (FRZ4 a) by lia. apply AG3. exact Ha. }
  assert (STK5 : L5C.stk (hl_sptop L) M5 sp 20480).
  { apply (L5C.stk_grows _ M4 M5 _ _ MG5). apply (L5C.stk_grows _ M3 M4 _ _ MG4 STK3). }
  pose proof (L5C.stk_writable RSEGS _ M5 sp _ STK5) as WR5.
  assert (DEFO5 : L5.defined M5 ois 272).
  { apply (L5C.defined_agree M2 M5); [intros i Hi; apply AG25; lia|]. apply (L5.defined_grows M1 M2 _ _ MG2). exact DEF1. }
  assert (WRO5 : L5.writable RSEGS M5 ois 272) by (apply (L5C.writable_of_defined RSEGS M5 ois 272 DEFO5); lia).
  assert (DEFB5 : L5.defined M5 B cap).
  { apply (L5.defined_grows M4 M5 _ _ MG5). apply (L5C.defined_agree M3 M4); [intros i Hi; apply FRZ4; lia| exact FDEF]. }
  LeanFeed.pfeed P (PMISP.icCl3_conc fx4 R6 M5 (fun j => match j with 2%nat => sp | 33%nat => ois | 39%nat => os - ois | 40%nat => n | 41%nat => B | 42%nat => cap - 1 | _ => 0 end)) ltac:(first [ PMK.sc | gx AG25 | (apply (L5C.writable_of_defined RSEGS M5 (B + n) 1); [apply (L5.defined_sub M5 B cap); [exact DEFB5|lia|lia]|lia|lia]) ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx6 & R7 & M6 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG6 & FR6 & FRZ6 & MS6 & KS6 & H1 & H2 & H8 & H9 & H10 & H18 & H19 & H20 & Z0 & Q96 & Q88 & Q80)); PMK.pvz_clrT.
  clear FR6 H1 H9 H10 H18 H19 H20.
  set (P6 := fun a => ois + 80 <= a < ois + 104 \/ B + n <= a < B + n + 1).
  assert (AG6 : forall a, 0 <= a < 2 ^ 64 -> ~ P6 a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P6 in NP. apply FRZ6; [exact Ha| |]; intros X; apply NP; lia. }
  assert (CW6 : forall a, P6 a -> PMK.cwr L LB3 a).
  { intros a Ha. unfold P6 in Ha. destruct Ha as [X|X]; [apply (PMK.cwr_stack L LB3 M5 sp 20480 a STK5); lia|].
    apply (PMK.cwr_block L LB3 B cap a); [left; reflexivity| lia]. }
  assert (DEC6 : forall a, {P6 a} + {~ P6 a}) by (intros a; unfold P6; apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB3 (debit L cr cap) M5 model3 fx4 fx6 R6 364132 R7 0x36248 M6 P6 K HH5 Mh3 Ml3 ltac:(lia) MS6 MG6 AG6 CW6 DEC6).
  intros HH6.
  (* [comment removed for export] *)
  destruct SI as (S8 & S16b & S24 & S32 & S40 & S48 & S56 & S64 & S72).
  destruct SB as (T88 & T96 & T104 & T112 & T120 & T128 & T136).
  assert (AG16 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (sp - 192 <= a < sp - 144) -> ~ (ois + 16 <= a < ois + 24) -> ~ (ois + 32 <= a < ois + 116) ->
            M6 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. rewrite (AG6 a) by (unfold P6; lia). rewrite (AG25 a) by lia. apply AG2; [lia| unfold P2; lia]. }
  assert (AG26 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (ois + 80 <= a < ois + 104) -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N1. rewrite (AG6 a) by (unfold P6; lia). apply AG25. exact Ha. }
  assert (V1 : 0 <= bv_unsigned (getr R0 (PMK.reg 1)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V8 : 0 <= bv_unsigned (getr R0 (PMK.reg 8)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V9 : 0 <= bv_unsigned (getr R0 (PMK.reg 9)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V18 : 0 <= bv_unsigned (getr R0 (PMK.reg 18)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V19 : 0 <= bv_unsigned (getr R0 (PMK.reg 19)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V20 : 0 <= bv_unsigned (getr R0 (PMK.reg 20)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V21 : 0 <= bv_unsigned (getr R0 (PMK.reg 21)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V22 : 0 <= bv_unsigned (getr R0 (PMK.reg 22)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V23 : 0 <= bv_unsigned (getr R0 (PMK.reg 23)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (CAP2 : cap mod 2 = 0) by (pose proof (Z.div_mod cap 8 ltac:(lia)); lia).
  pose proof (PMF.odd_byte cap CAP2 ltac:(lia)) as ODD.
  assert (U80 : L5.u8_at RSEGS M6 (ois + 80) ((cap + 1) mod 256)).
  { replace (cap + 1) with (cap - 1 + 2) by lia. apply (PMF.u8_of_u64 RSEGS M6 (ois + 80) (cap - 1 + 2) ltac:(lia) Q80). }
  assert (STK6 : L5C.stk (hl_sptop L) M6 sp 20480) by (apply (L5C.stk_grows _ M5 M6 _ _ MG6 STK5)).
  pose proof (L5C.stk_writable RSEGS _ M6 sp _ STK6) as WR6.
  assert (WRO6 : L5.writable RSEGS M6 ois 272) by (apply (L5.writable_grows RSEGS M5 M6 _ _ MG6); exact WRO5).
  LeanFeed.pfeed P (PMISP.icCl4_conc fx6 R7 M6 (fun j => match j with 2%nat => sp | 33%nat => ois | 38%nat => (cap + 1) mod 256 | 39%nat => os - ois
      | 40%nat => n | 41%nat => B
      | 43%nat => bv_unsigned (getr R0 (PMK.reg 1)) | 44%nat => bv_unsigned (getr R0 (PMK.reg 8)) | 45%nat => bv_unsigned (getr R0 (PMK.reg 9))
      | 46%nat => bv_unsigned (getr R0 (PMK.reg 18)) | 47%nat => bv_unsigned (getr R0 (PMK.reg 19)) | 48%nat => bv_unsigned (getr R0 (PMK.reg 20))
      | 49%nat => bv_unsigned (getr R0 (PMK.reg 21)) | 50%nat => bv_unsigned (getr R0 (PMK.reg 22)) | 51%nat => bv_unsigned (getr R0 (PMK.reg 23)) | _ => 0 end)) ltac:(first [ PMK.sc | exact ODD | gx AG16 | gx AG26 | (pose proof (Z.mod_pos_bound (cap + 1) 256 ltac:(lia)); lia) ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx7 & Rz & M7 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG7 & FR7 & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E18 & E19 & E20 & E21 & E22 & E23 & G104 & G48 & G40 & G32)); PMK.pvz_clrT.
  clear FR7 E10 E11 E12 E13 E14.
  set (P7 := fun a => sp - 192 <= a < sp - 144 \/ ois + 32 <= a < ois + 56 \/ ois + 104 <= a < ois + 112).
  assert (AG7 : forall a, 0 <= a < 2 ^ 64 -> ~ P7 a -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P7 in NP. apply FRZ7; [exact Ha| | |]; intros X; apply NP; lia. }
  assert (CW7 : forall a, P7 a -> PMK.cwr L LB3 a).
  { intros a Ha. apply (PMK.cwr_stack L LB3 M6 sp 20480 a STK6). unfold P7 in Ha. lia. }
  assert (DEC7 : forall a, {P7 a} + {~ P7 a}) by (intros a; unfold P7; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB3 (debit L cr cap) M6 model3 fx6 fx7 R7 0x36248 Rz 0x34ab8 M7 P7 K HH6 Mh3 Ml3 ltac:(lia) MS7 MG7 AG7 CW7 DEC7).
  intros HH7.
  (* [comment removed for export] *)
  eapply (L5.cps_of_msteps RSEGS); [exact Mh3| exact Ml3| apply (PMK.ret_to RSEGS fx7 Rz M7 0x34ab8 W_34744 r F_34744 ltac:(reflexivity) D_34744)|].
  { rewrite E1, Z_to_bv_bv_unsigned. exact Rra. } { exact RA1. } { exact RA2. }
  assert (STK7 : L5C.stk (hl_sptop L) M7 sp 20480) by (apply (L5C.stk_grows _ M6 M7 _ _ MG7 STK6)).
  assert (AG17 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (sp - 192 <= a < sp - 144) -> ~ (ois + 16 <= a < ois + 24) -> ~ (ois + 32 <= a < ois + 116) ->
            M7 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. rewrite (AG7 a) by (unfold P7; lia). apply AG16; lia. }
  assert (AG27 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (ois + 80 <= a < ois + 104) -> ~ (sp - 192 <= a < sp - 144) -> ~ (ois + 32 <= a < ois + 56)
            -> ~ (ois + 104 <= a < ois + 112) -> M7 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4. rewrite (AG7 a) by (unfold P7; lia). apply AG26; lia. }
  assert (AG67 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 192 <= a < sp - 144) -> ~ (ois + 32 <= a < ois + 56) -> ~ (ois + 104 <= a < ois + 112) ->
            M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. apply AG7; [exact Ha| unfold P7; lia]. }
  assert (MG57 : mem_grows M5 M7) by (intros x Hx; apply MG7, MG6; exact Hx).
  (* [comment removed for export] *)
  assert (EK34 : PMK.ek L LB sp 20480 [(ois, 272)] M3 M4).
  { intros a KA. apply FRZ4. destruct KA as (X & _). exact X. }
  assert (EK45 : PMK.ek L LB sp 20480 [(ois, 272)] M4 M5).
  { intros a KA. apply AG5; [destruct KA as (X & _); exact X|]. unfold P5.
    apply (L5C.kept_not_fresh L LB sp 20480 [(ois, 272)] a B cap KA FAP FBH FBC LBhi). }
  assert (EK56 : PMK.ek L LB sp 20480 [(ois, 272)] M5 M6).
  { intros a KA. apply AG6; [destruct KA as (X & _); exact X|]. unfold P6. intros [X|X].
    - destruct KA as (_ & _ & _ & O). apply (O (ois, 272)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    - apply (L5C.kept_not_fresh L LB sp 20480 [(ois, 272)] a B cap KA FAP FBH FBC LBhi). lia. }
  assert (EK67 : PMK.ek L LB sp 20480 [(ois, 272)] M6 M7).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M6 M7 P7 AG7 STK6 LBhi). intros a X. unfold P7 in X.
    destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
  assert (EK17 : PMK.ek L LB sp 20480 [(ois, 272)] M1 M7).
  { apply (PMK.ek_trans L LB sp 20480 _ M1 M2 M7 EK12). apply (PMK.ek_trans L LB sp 20480 _ M2 M3 M7 EK23).
    apply (PMK.ek_trans L LB sp 20480 _ M3 M4 M7 EK34). apply (PMK.ek_trans L LB sp 20480 _ M4 M5 M7 EK45).
    apply (PMK.ek_trans L LB sp 20480 _ M5 M6 M7 EK56 EK67). }
  assert (DK17 : PMK.dk L LB sp 20480 M1 M7).
  { apply (PMK.dk_trans L LB sp 20480 M1 M2 M7); [apply PMK.dk_grows; exact MG2|]. apply (PMK.dk_trans L LB sp 20480 M2 M3 M7 DK23).
    apply PMK.dk_grows. intros x Hx. apply MG57, MG5, MG4. exact Hx. }
  assert (DEFO7 : L5.defined M7 ois 272) by (apply (defined_dk LB sp 20480 M1 M7 ois 272 DK17 STK1); [lia|lia|lia|exact DEF1]).
  destruct HC as (H0 & H24 & H120 & H152 & H156 & H160 & H168 & H176).
  cbn [pa_vp_iss pa_classic_imp pa_vp_iss_ios AD PnLayoutS_u.ADDR_S] in H0, H24, H120, H168.
  apply (KONT fx7 Rz M7 model3 (PM.VLong cap n B) (PM.STRM B (B + n) 0) (debit L cr cap)).
  - apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
    assert (CH : forall j, In j PMIS.CSK -> getr Rz (PMK.reg j) = getr R0 (PMK.reg j)).
    { intros j Hj. rewrite (KS7 j (csk_icCl4 j Hj)), (KS6 j (csk_icCl3 j Hj)), (KS5 j (csk_CS j Hj)), (KS4 j (csk_icCl2 j Hj)).
      rewrite (PMK.cs_of_preserved R3 R4 j RP3 (csk_cs j Hj)). rewrite (KS2 j Hj). apply RCSK. exact Hj. }
    destruct Hk as [<-|Hk]; [rewrite E2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
    destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
    destruct Hk as [<-|Hk]; [rewrite E8; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E18; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E20; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E22; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
    repeat (destruct Hk as [<-|Hk]; [apply CH; PMK.inl|]). destruct Hk.
  - unfold PMIS.iss_at, PM.iss_at. cbn [pa_vp_iss pa_vp_strbuf pa_classic_imp pa_vp_iss_ios PM.vs_data PM.vs_size PM.sm_g PM.sm_eg PM.sm_st AD PnLayoutS_u.ADDR_S].
    split; [t14 AG17 H0|].
    split; [apply (L5.defined_sub M7 ois 272); [exact DEFO7|lia|lia]|].
    split; [exact I|].
    split; [t14 AG27 C16|].
    split; [t14 AG17 H24|].
    split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem|].
    split; [apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; apply AG27; lia|lia|lia|]; apply (PMCG.u64_of_zeros RSEGS M2); [|lia|lia];
            apply (PMCG.zeros_sub M2 (ois + 32) 48); [exact Z32|lia|lia]|].
    split.
    { split; [apply (L5.defined_sub M7 ois 272); [exact DEFO7|lia|lia]|]. split; [exact I|].
      split; [replace (cap + 1) with (cap - 1 + 2) by lia; t14 AG67 Q80|]. split; [t14 AG67 Q88|]. split; [t14 AG67 Q96|].
      split; [lia|]. split; [lia|]. split; [exact CAP2|]. split; [|exact I].
      apply (L5.defined_grows M5 M7 _ _ MG57). exact DEFB5. }
    split; [PMK.gmem|].
    split; [t14 AG27 C112|].
    split.
    { unfold PM.iosb_at. cbn [pa_classic_imp AD PnLayoutS_u.ADDR_S].
      split; [t14 AG17 H120|]. split; [t14 AG17 H152|]. split; [t14 AG17 H156|]. split; [t14 AG17 H160|].
      split; [t14 AG17 H168|]. split; [t14 AG17 H176|].
      split; [apply (L5.defined_sub M7 ois 272); [exact DEFO7|lia|lia]|].
      split; [exact I| left; reflexivity]. }
    split; lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M1 M7 EK17 true); [|exact LOC1].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW.
  - apply PMK.hpres_of.
    + apply (PMK.ek_trans L LB sp 20480 _ M0 M1 M7 EK01).
      apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 (PMIS.WF ois b) [(ois, 272)] M1 M7 EK17 (incl_refl _)); [intros x Hx; exact Hx|].
      apply outside_WF_ois.
    + destruct STK7 as (_ & _ & _ & _ & X). exact X.
    + apply (PMK.dk_trans L LB sp 20480 M0 M1 M7 DK01 DK17).
  - unfold PMSP.credit_keep, PMIS.cost, PMSP.cr0, PM.cost1, debit. cbn [fst snd PM.vs_size]. lia.
  - apply (L5C.model_but_vm_trans _ _ _ MB1 MB3).
  - cbn [PM.vs_own app]. exact HH7.
Qed.

End Stage.
End PMIS3.
