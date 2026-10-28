(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatAllocA_b BatAllocB_b BatAllocG_b BatAllocV_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsPop3_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b BatAllocPre3_b BatAllocPost_b BatAllocate3_b
     BatAllocA16_b BatAllocB16_b BatAllocPre3A16_b BatAllocPostA16_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_alloc3_fp16 (sp t spb ris qs c km ab rz n rs l2 blk : Z) (x : Z) : Prop :=
  (sp - 1920 <= x < sp) \/ art_ca_fp (sp - 128) t spb ris qs c km x
  \/ (ab <= x < ab + rz + n) \/ (2147450880 + (ab + rz) / 8 <= x < 2147450880 + (ab + rz) / 8 + rs / 8)
  \/ (t + 2800 <= x < t + 2824) \/ (t + 2912 + 8 * c <= x < t + 2920 + 8 * c) \/ dprivD l2 blk x.

Lemma art_alloc3_fp16_sub : forall sp t spb ris qs c km ab rz n rs l2 blk x,
  art_alloc3_fp16 sp t spb ris qs c km ab rz n rs l2 blk x -> art_alloc3_fp sp t spb ris qs c km ab rz n rs l2 blk x.
Proof.
  intros sp t spb ris qs c km ab rz n rs l2 blk x F. unfold art_alloc3_fp16 in F. unfold art_alloc3_fp.
  destruct F as [F|F]; [left; lia|right; exact F].
Qed.

(* [comment removed for export] *)
Lemma art_alloc3_fp16_window : forall S t spb ris qs c km ab rz n rs l2 blk x,
  art_alloc3_fp16 (S - 2176) t spb ris qs c km ab rz n rs l2 blk x ->
  (S - 4096 <= x < S) \/ art_alloc3_fp (S - 2144) t spb ris qs c km ab rz n rs l2 blk x.
Proof.
  intros S t spb ris qs c km ab rz n rs l2 blk x F. unfold art_alloc3_fp16 in F. unfold art_alloc3_fp.
  destruct F as [F|[F|F]]; [left; lia| |right; right; right; exact F].
  unfold art_ca_fp in F |- *. destruct F as [F|[F|F]]; [left; lia| |right; right; left; right; right; exact F].
  unfold art_refill_fp in F |- *. destruct F as [F|F]; [left; lia|]. right; right; left; right; left; right; exact F.
Qed.

Lemma art_hdr_b1_type_16 : forall ob, 0 <= ob < 256 -> Z.land (art_hdr_b1_16 ob) 243 mod 4 = 1 /\ 0 <= Z.land (art_hdr_b1_16 ob) 243 < 256.
Proof.
  intros ob Hob.
  assert (H : forallb (fun o => (Z.land (art_hdr_b1_16 o) 243 mod 4 =? 1) && (0 <=? Z.land (art_hdr_b1_16 o) 243) && (Z.land (art_hdr_b1_16 o) 243 <? 256)) (AsanTab.zrange 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H ob ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; lia)).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem art_allocate3_16 :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M0 rom : word -> option byte) (raw : word)
         (sp HI n stk tp key tsd ctx t loff spb ris qs km l2 blk trp szt rl rz qz rs qr qn m8 q16 : Z) (kb : nat) (inited : bool) (cl : art_cls),
    let c := AsanTab.class_id (rs + 16 + rz) in
    let w := art_ca_cptr c cl in
    let ab := spb + c * 2 ^ 32 + w * 16 in
    let shb := 2147450880 + 8192 * qs + c * 2 ^ 29 in
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 1295832 ->
    getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 16 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
    (* [comment removed for export] *)
    8 <= n -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> rs = 16 * q16 -> n <= rs <= n + 7 -> rs + 16 + rz <= 65536 ->
    (* [comment removed for export] *)
    art_geo HI t ctx tp tsd spb ris qs -> HI <= sp - 1920 -> HI + 4096 <= sp -> sp + 2144 <= 2 ^ 47 -> sp <= stk -> stk + 16 <= sp + 4096 ->
    0 <= trp < 2 ^ 64 -> 0 <= szt < 2 ^ 64 -> sp <= trp -> trp + 8 * szt <= sp + 4096 ->
    0 <= loff -> 0x10000 <= tp + loff -> tp + loff + 4 <= 0x696000 -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->     (* [comment removed for export] *)
    (* [comment removed for export] *)
    l2 + 2 ^ 20 <= HI -> blk + 2 ^ 23 <= HI ->
    apart l2 (2 ^ 20) t 4096 -> apart l2 (2 ^ 20) ctx 4096 -> apart l2 (2 ^ 20) spb (2 ^ 37 + 4096) -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    apart blk (2 ^ 23) t 4096 -> apart blk (2 ^ 23) ctx 4096 -> apart blk (2 ^ 23) spb (2 ^ 37 + 4096) -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
    (* [comment removed for export] *)
    wrA M0 (sp - 1920) 1920 -> wrA M0 t 4096 -> wrA M0 (2147450880 + 8192 * qs) (2 ^ 34) ->
    art_alloc_rodata M0 -> cellA M0 0x104c0 1 4 -> art_rz_rodata M0 -> art_layout M0 -> art_tsd M0 tp key tsd ctx t -> art_prim_consts spb ris M0 ->
    cellA M0 0x140918 1 1 -> cellA M0 0x1c1ea2 1 0 -> cellA M0 (1295832 + 3616) 8 (2 ^ 40) -> cellA M0 (1295832 + 3624) 2 16 -> cellA M0 (1295832 + 3626) 2 2048 ->
    cellA M0 0x1d1700 8 0 -> cellA M0 (0x13d438 + 44) 4 4096 -> cellA M0 (0x13d438 + 52) 4 190 -> cellA M0 (0x13d438 + 85) 1 1 ->
    cellA M0 0x138120 8 loff -> cellA M0 (tp + loff) 4 0 -> cellA M0 t 8 ctx -> cellA M0 (ctx + 8) 4 0 ->
    cellA M0 stk 8 trp -> cellA M0 (stk + 8) 8 szt ->
    (* [comment removed for export] *)
    art_pc_hdr (t + 208) inited M0 -> art_cls_rep (t + 208) spb ris c cl M0 -> art_cls_ok c cl -> (cl_cache cl <> [] -> inited = true) -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events spb c cl) ->
    (* [comment removed for export] *)
    (forall y, cl_au cl <= 8 * y < cl_mu cl -> cellA M0 (shb + y) 1 250) ->
    (forall v, In v (cl_cache cl ++ cl_free cl) -> cellA M0 (shb + 2 * v) 1 250) ->
    (* [comment removed for export] *)
    DInvD l2 blk (S kb) M0 -> DPreD blk M0 trp szt -> DRoD M0 ->
    (forall regs' (M' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
        mem_grows M0 M' ->
        (forall x : word, ~ art_alloc3_fp16 sp t spb ris qs c km ab rz n rs l2 blk (U x) -> M' x = M0 x) ->
        DInvD l2 blk kb M' ->
        art_pc_hdr (t + 208) true M' -> art_cls_rep (t + 208) spb ris c (art_cls_pop (art_ca_pre c cl)) M' -> art_cls_ok c (art_cls_pop (art_ca_pre c cl)) ->
        art_cptr_ok (AsanTab.class_size c) (cl_au (art_ca_pre c cl)) w ->
        0 <= b1 < 256 -> b1 mod 4 = 1 ->
        cellA M' (ab + rz - 16) 1 2 -> cellA M' (ab + rz - 15) 1 b1 -> cellA M' (ab + rz - 14) 2 0 -> cellA M' (ab + rz - 12) 4 n ->
        cellA M' (shb + 2 * w) 1 250 ->
        (forall j, 0 <= j < qn -> cellA M' (shb + 2 * w + 2 * qz + j) 1 0) -> (m8 <> 0 -> cellA M' (shb + 2 * w + 2 * qz + qn) 1 m8) ->
        (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
           forall j, 0 <= j < 32768 -> ~ (2 * w + 2 * qz <= 32768 * km + j < 2 * w + 2 * qz + qr) -> cellA M' (shb + 32768 * km + j) 1 250) ->
        (rz <> 16 -> cellA M' ab 8 0xcc6e96b9cc6e96b9 /\ cellA M' (ab + 8) 8 (ab + rz - 16)) ->          (* [comment removed for export] *)
        Q (log ++ art_ca_events spb c cl) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x525e4 : word) M0 rom).
Proof.
  intros Q log regs M0 rom raw sp HI n stk tp key tsd ctx t loff spb ris qs km l2 blk trp szt rl rz qz rs qr qn m8 q16 kb inited cl c w ab shb
         H1 Hret H2 H4 H10 H11 H12 H13 H14 H15
         Hn Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim
         GEO HHI HHI' Hsp' Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd
         Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
         W Wt Wsh RO C1046 RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Ctrp Cszt
         PH RC OK Hin Emu Room EV PZ1 PZ2 DI DP DR K.
  assert (Eab : ab = spb + c * 2 ^ 32 + w * 16) by reflexivity.
  assert (Eshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29) by reflexivity.
  clearbody ab shb.
  pose proof (AsanTab.class_id_ok (rs + 16 + rz) ltac:(lia)) as (Hc & Hfit & _). fold c in Hc, Hfit.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in G15.
  clear G10 G16.
  pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
  assert (Hkm : 0 <= km) by lia.
  assert (Hkm' : 262144 * km <= 3758096384) by lia.
  pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  (* [comment removed for export] *)
  assert (Hq16 : (n + 15) / 16 = q16). { symmetry. apply (Z.div_unique _ 16 q16 (n + 15 - 16 * q16)); lia. }
  assert (Ers_max : rs = (Z.max n 8 + 15) / 16 * 16) by (rewrite Z.max_l by lia; rewrite Hq16; lia).
  destruct (art_allocate_pre3a_16 regs M0 rom raw sp 1295832 n stk tp key tsd ctx t rl rs qr rz qz
              H1 H2 H4 H10 H11 H12 H13 H14 H15 ltac:(lia) Erl Erz Erz16 Hqz
              Ers_max Ers ltac:(rewrite Z.max_l by lia; lia) Hprim
              ltac:(lia) Hsp' Hstk Hstk' ltac:(lia) ltac:(lia)
              G7 ltac:(lia) G9 ltac:(unfold apart; lia) ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22
              W RO C1046 RZRO TSD Ci Cr Cmax Cmin16 Cmax2048)
    as (r5 & M5 & RUN5 & P5_1 & P5_2 & P5_4 & P5_8 & P5_9 & P5_10 & P5_11 & P5_12 & P5_13 & P5_19 & P5_20 & P5_21 & P5_22 & P5_23 & P5_25 & P5_26 & P5_27 & P5_3
        & G05 & AG05 & F120 & F112 & F104 & F96 & F88 & F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F8 & F16).
  eapply ar_steps; [exact RUN5|].
  assert (A05 : art_agree [(sp - 144, 144)] M0 M5). { intros x Hx. apply AG05. cbn in Hx. lia. }
  assert (W5 : wrA M5 (sp - 128 - 720) 720) by (eapply wr_grows; [exact G05|]; eapply wr_sub; [exact W|lia|lia]).
  assert (Wt5 : wrA M5 t 4096) by (eapply wr_grows; [exact G05|exact Wt]).
  assert (Wsh5 : wrA M5 (2147450880 + 8192 * qs) (2 ^ 34)) by (eapply wr_grows; [exact G05|exact Wsh]).
  assert (PC5 : art_prim_consts spb ris M5). { eapply art_prim_consts_fp; [exact A05| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
  assert (L5 : art_layout M5). { eapply art_layout_fp; [exact A05| |exact L]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
  assert (T5 : art_tsd M5 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A05| | |exact G19|exact G20|exact G21|exact G22|exact TSD].
    - intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
    - intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
  assert (PH5 : art_pc_hdr (t + 208) inited M5).
  { apply (art_pc_hdr_tr _ (t + 208) inited M0 M5 ltac:(lia) ltac:(lia) A05); [|exact PH]. intros c' Hc'. clear - Hc' HHI G7 G8. zarith_f. }
  assert (RC5 : art_cls_rep (t + 208) spb ris c cl M5).
  { apply (art_cls_rep_tr [(sp - 144, 144)] (t + 208) spb ris c cl M0 M5); first [ exact RC | exact G05 | exact A05 | exact Hl16 | lia | idtac ];
      clear - Hc HHI Hsp' G1 G2 G6 Eris G4 Espb G7 G8 Hnf4 Hmfa1; zarith_f. }
  assert (Hs8 : (rs + 16 + rz) mod 8 = 0). { rewrite Ers, Erz16. replace (8 * qr + 16 + 16 * qz) with ((qr + 2 + 2 * qz) * 8) by lia. apply Z_mod_mult. }
  (* [comment removed for export] *)
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  apply (art_ca_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r5 M5 rom (0x52884 : bv 64)%bv (sp - 128) HI t ctx tp key tsd spb ris qs (rs + 16 + rz) km inited cl
           P5_1 ltac:(unfold ret_ok; bveq) P5_2 P5_4 P5_10 P5_11 P5_12 P5_13 ltac:(lia) Hs8 ltac:(lia) ltac:(lia) GEO W5 Wt5 PC5 L5 T5 PH5 RC5 OK Hin Emu).
  { intros E1 E2. destruct (Room E1 E2) as (R1 & R2). split; [exact R1|]. split; [exact R2|].
    split; (eapply wr_sub; [exact Wsh5| |]); clear - Hc Hkm R1 Emu; lia. }
  { exact EV. }
  intros r6 M6 R10 R2 R1 RK G56 RA RPH RCR ROK RCP RSH.
  fold c in R10, RA, RCR, ROK, RCP, RSH. fold w in R10, RCP.
  (* [comment removed for export] *)
  set (clp := art_ca_pre c cl) in *.
  assert (R6_10 : getr r6 10 = Z_to_bv 64 ab) by (rewrite Eab; exact R10).
  pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16). set (sz := AsanTab.class_size c) in *.
  pose proof RCP as (Hw0 & Hwsz & _).
  pose proof ROK as OK'. unfold art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'.
  destruct OK' as (Hl16' & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (_ & Hmfa1') & Hnf4' & _).
  set (au' := cl_au clp) in *. set (mu' := cl_mu clp) in *.
  destruct RCR as [CR6 RR6]. pose proof RR6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu6).
  cbn [art_cls_pop cl_mu] in Wu6. fold mu' in Wu6.
  assert (A56 : art_agree (art_ca_W (sp - 128) t spb ris qs c km) M5 M6) by (apply art_ca_fp_agree; [exact Hc|exact RA]).
  unfold art_ca_W in A56.
  assert (G06 : mem_grows M0 M6) by (eapply mem_grows_trans; [exact G05|exact G56]).
  assert (Hab16 : ab mod 16 = 0). { rewrite Eab, Espb. replace (65536 * qs + c * 2 ^ 32 + w * 16) with ((4096 * qs + c * 2 ^ 28 + w) * 16) by lia. apply Z_mod_mult. }
  assert (Hrz16 : rz mod 16 = 0). { rewrite Erz16, Z.mul_comm. apply Z_mod_mult. }
  assert (Hab8 : ab / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w). { rewrite Eab, Espb. replace (65536 * qs + c * 2 ^ 32 + w * 16) with ((8192 * qs + c * 2 ^ 29 + 2 * w) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz). { rewrite Eab, Espb, Erz16. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
  (* [comment removed for export] *)
  assert (SAB6 : cellA M6 (shb + 2 * w) 1 250).
  { assert (OLD : 16 * w < cl_mu cl -> cellA M0 (shb + 2 * w) 1 250 -> cellA M6 (shb + 2 * w) 1 250).
    { intros Hold C0. apply (art_cell_tr1 _ M5 M6 _ _ _ A56); [|apply (art_cell_tr1 _ M0 M5 _ _ _ A05); [|exact C0]].
      - clear - Hold Emu HHI G1 G2 G4 G6 Espb Eris At_s Eshb Hc Hkm Hw0 Hmu3. zarith_f.
      - clear - HHI G1 G2 G4 G6 Espb Eris Eshb Hc Hw0 Hold Hmu3. zarith_f. }
    pose proof (art_ca_cptr_origin c cl Hc OK) as ORG. fold w in ORG. destruct ORG as [Hold|(Ecache & NP & Hauw)].
    - apply OLD; [|apply PZ2; exact Hold].
      pose proof (proj1 (Forall_forall _ _) Hfor w Hold) as (_ & Ho & _). fold sz in Ho. clear - Ho Haumu Hsz. lia.
    - destruct (Z_lt_ge_dec (16 * w) (cl_mu cl)) as [Hlo|Hhi].
      + apply OLD; [exact Hlo|]. apply PZ1. clear - Hauw Hlo. lia.
      + pose proof (art_ca_pre_mu_pop c cl Ecache NP) as Emu'. fold clp in Emu'. fold mu' in Emu'.
        pose proof (RSH Ecache NP (2 * w - 32768 * km) ltac:(clear - Hhi Emu Hwsz Haumu' Emu' Hsz; lia)) as C6.
        replace (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + (2 * w - 32768 * km)) with (shb + 2 * w) in C6 by (clear - Eshb; lia). exact C6. }
  (* [comment removed for export] *)
  assert (Wc6 : wrA M6 ab (rs + rz)). { eapply wr_sub; [exact Wu6| |]; clear - Eab Hw0 Hwsz Haumu' Hfit; lia. }
  destruct (art_cell_exists_b M6 (ab + rz - 15) 1 ltac:(lia) ltac:(right; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
              ltac:(eapply wr_sub; [exact Wc6| |]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)) as (ob & Hob & Cob).
  change (2 ^ (8 * Z.of_nat 1)) with 256 in Hob.
  assert (R6_9 : getr r6 9 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_9).
  assert (R6_19 : getr r6 19 = Z_to_bv 64 (rs + 16 + rz)) by (rewrite RK by inl; exact P5_19).
  assert (R6_20 : getr r6 20 = Z_to_bv 64 rz) by (rewrite RK by inl; exact P5_20).
  assert (R6_21 : getr r6 21 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_21).
  assert (R6_23 : getr r6 23 = Z_to_bv 64 stk) by (rewrite RK by inl; exact P5_23).
  assert (R6_25 : getr r6 25 = Z_to_bv 64 15) by (rewrite RK by inl; exact P5_25).
  assert (R6_26 : getr r6 26 = Z_to_bv 64 t) by (rewrite RK by inl; exact P5_26).
  assert (R6_27 : getr r6 27 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_27).
  assert (R6_4 : getr r6 4 = Z_to_bv 64 tp) by (rewrite RK by inl; exact P5_4).
  assert (R6_8 : getr r6 8 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_8).
  assert (R6_3 : getr r6 3 = getr regs 3) by (rewrite RK by inl; exact P5_3).
  assert (F16_6 : cellA M6 (sp - 128 + 16) 8 32) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
  assert (Ctctx6 : cellA M6 t 8 ctx) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
  assert (Ctid6 : cellA M6 (ctx + 8) 4 0) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
  assert (Ctrp6 : cellA M6 stk 8 trp) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
  assert (Cszt6 : cellA M6 (stk + 8) 8 szt) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
  pose proof (art_alloc_b_16_fn r6 M6 rom (sp - 128) ab n rs rz stk t ctx ob trp szt R2 R6_10 R6_9 R6_19 R6_20 R6_21 R6_23 R6_25 R6_26 R6_27
                ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hab16 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Ers_max ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hrz16 Hprim
                ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G13 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hob Htrp Hszt
                ltac:(eapply wr_sub; [exact Wc6| |]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
                Cob F16_6 Ctctx6 Ctid6 Ctrp6 Cszt6
                ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f)) as RUN7.
  match type of RUN7 with msteps _ _ (mkst ?R _ ?MM _) => set (R7 := R) in RUN7; set (M7 := MM) in RUN7 end.
  eapply ar_steps; [exact RUN7|].
  assert (A67 : art_agree [(ab + rz - 16, 16)] M6 M7).
  { unfold M7, art_alloc_memB_16. clear - Eab Espb G4 G2 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hsz Hqz Erz16. eapply art_agree_sub; [zagree|]. zsub_c ltac:(clear). }
  assert (G67 : mem_grows M6 M7) by (unfold M7, art_alloc_memB_16; zgrows).
  assert (Hn32 : n / 2 ^ 32 = 0) by (apply Z.div_small; clear - Hn Hrs Hprim Hqz Erz16; lia).
  pose proof (art_hdr_b1a_range ob Hob) as Hb1a. pose proof (art_hdr_b1_16_range ob Hob) as Hb1.
  assert (B7 : cellA M7 (ab + rz - 15) 1 (art_hdr_b1_16 ob) /\ cellA M7 (ab + rz - 12) 4 n /\ cellA M7 (ab + rz - 14) 2 0).
  { unfold M7, art_alloc_memB_16. rewrite Hn32. clear - Hb1a Hb1 Eab Espb G4 G2 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hsz Hqz Erz16 Hn Hprim Hrs. repeat split; zcell. }
  destruct B7 as (B7a & B7b & B7c).
  assert (G07 : mem_grows M0 M7) by (eapply mem_grows_trans; [exact G06|exact G67]).
  (* [comment removed for export] *)
  pose proof (art_agree_trans _ _ _ _ _ A05 (art_agree_trans _ _ _ _ _ A56 A67)) as A07.
  assert (DO7 : forall z, dprivD l2 blk z -> art_out ([(sp - 144, 144)] ++ [(sp - 128 - 720, 720); (t + 208, 2592); (t + 2872, 16); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 262144 * km, 262144);
                   (spb + c * 2 ^ 32 + 3758096384, 536870912); (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768);
                   (2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864)] ++ [(ab + rz - 16, 16)]) z).
  { apply art_dpriv_out; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (DI7 : DInvD l2 blk (S kb) M7). { apply (DInvD_frame l2 blk (S kb) M0 M7 DI). intros x Dx. apply A07. apply DO7. exact Dx. }
  assert (DP7 : DPreD blk M7 trp szt).
  { apply (DPreD_frame blk M0 M7 trp szt DP). intros x Hx. apply A07. apply (art_gap_out _ trp (8 * szt)); [|exact Hx]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (DR7 : DRoD M7).
  { apply (DRoD_frame M0 M7 DR). intros x Hx. apply A07. apply (art_gap_out _ 0x10000 (0x211b08 - 0x10000)); [|clear - Hx; lia]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (W7 : wrA M7 (sp - 128 - 224) 224) by (eapply wr_grows; [exact G07|]; eapply wr_sub; [exact W|lia|lia]).
  assert (ND7 : nodp (dprivD l2 blk) (sp - 128 - 224) 224). { intros i Hi D. unfold dprivD in D. clear - Hi D HHI G1 Dl2 Dblk. lia. }
  pose proof (art_depot_spec_holds l2 blk) as DEPOT. unfold art_depot_spec in DEPOT.
  destruct (DEPOT kb R7 M7 rom (0x52990 : bv 64)%bv (sp - 128) trp szt ltac:(unfold R7; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold R7; gres; exact R2)
              ltac:(unfold R7; gres; reflexivity) ltac:(unfold R7; gres; reflexivity) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) W7 ND7 DI7 DP7 DR7)
    as (r8 & M8 & id & RUN8 & P8_10 & Hid & K8 & G78 & AGd & DI8).
  clear DEPOT A07 DO7.
  eapply ar_steps; [exact RUN8|].
  assert (A78 : art_agree [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)] M7 M8).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply AGd; [unfold dprivD; clear - Hx; lia | clear - Hx; lia]. }
  (* [comment removed for export] *)
  pose proof (art_agree_trans _ _ _ _ _ A67 A78) as A68.
  pose proof (art_agree_trans _ _ _ _ _ A56 A68) as A58.
  pose proof (art_agree_trans _ _ _ _ _ A05 A58) as A08.
  assert (G08 : mem_grows M0 M8) by (eapply mem_grows_trans; [exact G07|exact G78]).
  assert (T_img : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x211b08 -> cellA M0 a k v -> cellA M8 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M8 a k v A08); [|exact C]. revert Ha Hk. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Ha Hk. zarith_f. }
  assert (T_frm : forall a (k : nat) v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M5 a k v -> cellA M8 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr1 _ M5 M8 a k v A58); [|exact C]. revert Ha Hk. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Ha Hk. zarith_f. }
  assert (W8 : wrA M8 (sp - 1920) 1920) by (eapply wr_grows; [exact G08|exact W]).
  assert (Wc8 : wrA M8 ab (rs + rz)) by (eapply wr_grows; [exact G78|]; eapply wr_grows; [exact G67|exact Wc6]).
  assert (Wsh8 : wrA M8 (0x7fff8000 + ab / 8) 8192). { eapply wr_grows; [exact G08|]. eapply wr_sub; [exact Wsh| |]; rewrite Hab8; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia. }
  assert (Wt8 : wrA M8 t 4096) by (eapply wr_grows; [exact G08|exact Wt]).
  assert (L8 : art_layout M8).
  { eapply art_layout_fp; [exact A08| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x211b08 - 0x10000)); [|clear - Hz; lia]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (T8 : art_tsd M8 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M8 tp key tsd ctx t A08); [| | | |exact TSD]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (SAB8 : cellA M8 (0x7fff8000 + ab / 8) 1 250).
  { rewrite Hab8. replace (0x7fff8000 + (8192 * qs + c * 2 ^ 29 + 2 * w)) with (shb + 2 * w) by (clear - Eshb; lia).
    apply (art_cell_tr1 _ M6 M8 _ _ _ A68); [|exact SAB6]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (Clsan8 : cellA M8 (tp + loff) 4 0). { apply (art_cell_tr1 _ M0 M8 _ _ _ A08); [|exact Clsan]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (RO3 : cellA M0 0x10360 8 0xcc6e96b9cc6e96b9) by (unfold art_alloc_rodata in RO; tauto).
  destruct (art_tcell_exists M8 t 2800 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mc & Hmc & Cmc).
  destruct (art_tcell_exists M8 t 2808 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mb & Hmb & Cmb).
  destruct (art_tcell_exists M8 t 2816 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mr & Hmr & Cmr).
  destruct (art_tcell_exists M8 t (2912 + 8 * c) At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - Hc; lia) ltac:(clear - Hc; lia) Wt8) as (mbs & Hmbs & Cmbs).
  replace (t + 2808) with (t + 2800 + 8) in Cmb by (clear; lia). replace (t + 2816) with (t + 2800 + 16) in Cmr by (clear; lia).
  replace (t + (2912 + 8 * c)) with (t + 2800 + 112 + 8 * c) in Cmbs by (clear; lia).
  assert (B8a : cellA M8 (ab + rz - 15) 1 (art_hdr_b1_16 ob)). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7a]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (B8b : cellA M8 (ab + rz - 12) 4 n). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7b]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (B8c : cellA M8 (ab + rz - 14) 2 0). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7c]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
  assert (R8_2 : getr r8 2 = Z_to_bv 64 (sp - 128)) by (rewrite K8 by dk8; unfold R7; gres; exact R2).
  assert (R8_3 : getr r8 3 = getr regs 3) by (rewrite K8 by dk8; unfold R7; gres; exact R6_3).
  assert (R8_4 : getr r8 4 = Z_to_bv 64 tp) by (rewrite K8 by dk8; unfold R7; gres; exact R6_4).
  assert (R8_8 : getr r8 8 = Z_to_bv 64 1) by (rewrite K8 by dk8; unfold R7; gres; exact R6_8).
  assert (R8_9 : getr r8 9 = Z_to_bv 64 n) by (rewrite K8 by dk8; unfold R7; gres; exact R6_9).
  assert (R8_18 : getr r8 18 = Z_to_bv 64 ab) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_19 : getr r8 19 = Z_to_bv 64 (rs + 16 + rz)) by (rewrite K8 by dk8; unfold R7; gres; exact R6_19).
  assert (R8_20 : getr r8 20 = Z_to_bv 64 (ab + rz)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_21 : getr r8 21 = Z_to_bv 64 (ab + rz - 16)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_24 : getr r8 24 = Z_to_bv 64 0) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  destruct (art_allocate_post_16 r8 M8 rom raw sp n qn m8 rs qr rz qz c (4096 * qs) w ab t tp loff key tsd ctx id 250 (art_hdr_b1_16 ob) mc mb mr mbs
              (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
              (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25)) (U (getr regs 26)) (U (getr regs 27))
              eq_refl Hret R8_2 R8_4 R8_8 R8_9 P8_10 R8_18 R8_19 R8_20 R8_21 R8_24
              Hn En Hm8 Ers Hrs Erz16 ltac:(clear - Hqz Erz16; lia) Hprim eq_refl ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
              ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hsp'
              G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G9 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - At_s; unfold apart in *; lia)
              ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) G15 G18 ltac:(clear - Ac_s; unfold apart in *; lia)
              Hloff G19 Hloff' Hloff'' G21 G22
              ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f)
              Hid ltac:(lia) Hb1 Hmc Hmb Hmr Hmbs
              (u64_range raw) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
              W8 Wc8 Wsh8 Wt8 L8 T8 SAB8
              ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cpp]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cmfs]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cfb])
              ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cg]) Clsan8 ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Chook]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact RO3])
              Cmc Cmb Cmr Cmbs B8a B8b B8c
              ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F8])
              ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F120]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F112]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F104])
              ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F96]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F88]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F80])
              ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F72]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F64]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F56])
              ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F48]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F40]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F32])
              ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F24]))
    as (rF & MF & RUNF & PF10 & PF2 & PF1 & PF8 & PF9 & PF18 & PF19 & PF20 & PF21 & PF22 & PF23 & PF24 & PF25 & PF26 & PF27 & GF & AGF & CL1 & CL2 & CL3 & CL4 & SHZ & SHP & PF3 & PF4 & LCH).
  eapply ar_steps; [exact RUNF|]. apply ar_done.
  assert (A8F : art_agree [(sp - 1920, 1920); (ab, rz + n); (2147450880 + (ab + rz) / 8, rs / 8); (t + 2800, 24); (t + 2912 + 8 * c, 8)] M8 MF).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply AGF. unfold art_post_writtenG16. clear - Hx. lia. }
  rewrite Hub8, Hqr8 in A8F.
  pose proof (art_agree_trans _ _ _ _ _ A68 A8F) as A6F.
  assert (G6F : mem_grows M6 MF) by (eapply mem_grows_trans; [exact G67|]; eapply mem_grows_trans; [exact G78|exact GF]).
  pose proof (art_hdr_b1_type_16 ob Hob) as (Hty & Hb1').
  apply (K rF MF (Z.land (art_hdr_b1_16 ob) 243)).
  - exact PF10.
  - exact PF2.
  - exact PF1.
  - intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      [ rewrite PF3; exact R8_3 | rewrite PF4, R8_4; symmetry; exact H4
      | rewrite PF8 | rewrite PF9 | rewrite PF18 | rewrite PF19 | rewrite PF20 | rewrite PF21 | rewrite PF22 | rewrite PF23 | rewrite PF24 | rewrite PF25 | rewrite PF26 | rewrite PF27 ];
      apply Z_to_bv_bv_unsigned.
  - eapply mem_grows_trans; [exact G08|exact GF].
  - intros x N.
    assert (N1 : ~ art_post_writtenG16 sp t c ab rz n rs (U x)).
    { intros F; apply N; unfold art_alloc3_fp16; unfold art_post_writtenG16 in F.
      destruct F as [F|[F|[F|[F|F]]]]; [left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left]; exact F. }
    rewrite (AGF x N1).
    rewrite (AGd x) by (intros F; apply N; unfold art_alloc3_fp16; first [ do 6 right; exact F | left; clear - F; lia ]).
    rewrite (A67 x) by (cbn [art_out fst snd]; split; [|exact I]; intros F; apply N; unfold art_alloc3_fp16; right; right; left; clear - F Hqz Erz16 Hn; lia).
    rewrite (RA x) by (intros F; apply N; unfold art_alloc3_fp16; right; left; exact F).
    apply AG05. intros F. apply N. unfold art_alloc3_fp16. left. clear - F. lia.
  - apply (DInvD_frame l2 blk kb M8 MF DI8). intros x Dx. apply A8F. revert Dx. apply art_dpriv_out; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f.
  - apply (art_pc_hdr_tr _ (t + 208) true M6 MF ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) A6F); [|exact RPH]. intros c' Hc'. revert Hc'. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Hc'. zarith_f.
  - match type of A6F with art_agree ?WW _ _ => apply (art_cls_rep_tr WW (t + 208) spb ris c (art_cls_pop clp) M6 MF) end; first [ exact (conj CR6 RR6) | exact G6F | exact A6F | exact Hl16' | idtac ];
      cbn [art_cls_pop cl_free]; first [ clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia | clear - Hnf4' Hmfa1'; lia | idtac ].
    all: revert Hnf4' Hmfa1'; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; intros Hnf4' Hmfa1'; zarith_f.
  - exact ROK.
  - exact RCP.
  - exact Hb1'.
  - exact Hty.
  - exact CL1.
  - exact CL3.
  - exact CL4.
  - exact CL2.
  - apply (art_cell_tr1 _ M6 MF _ _ _ A6F); [|exact SAB6]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f.
  - intros j Hj. replace (shb + 2 * w + 2 * qz + j) with (2147450880 + ab / 8 + 2 * qz + j) by (rewrite Hab8; clear - Eshb; lia). apply SHZ. exact Hj.
  - intros NE. replace (shb + 2 * w + 2 * qz + qn) with (2147450880 + ab / 8 + 2 * qz + qn) by (rewrite Hab8; clear - Eshb; lia). apply SHP. exact NE.
  - intros E1 E2 j Hj Hex. pose proof (RSH E1 E2 j Hj) as C6.
    replace (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) with (shb + 32768 * km + j) in C6 by (clear - Eshb; lia).
    apply (art_cell_tr1 _ M6 MF _ _ _ A6F); [|exact C6]. revert Hj Hex. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Hj Hex. zarith_f.
  - exact LCH.
Qed.
End Spec.
