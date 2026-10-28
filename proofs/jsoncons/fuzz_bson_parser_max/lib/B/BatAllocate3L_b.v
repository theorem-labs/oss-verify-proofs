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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatAllocA_b BatAllocB_b BatAllocG_b BatAllocV_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatCellEx_b BatDepotA_b BatDepot_b BatAllocate3_b BatSecAllocPost_b BatSecRSpec_b BatCASecR_b BatAllocPre3L_b BatAllocSecB_b BatAllocPostL_b.
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
Definition art_alloc3L_fp (sp t parr nch r msz l2 blk : Z) (committed : bool) : list (Z * Z) :=
  [ (sp - 1952, 1952); (0x13c618, 624); (0x13c888 + 16, 16); (t + 2800, 112); (r, msz); (art_shlo r, art_shhi r msz - art_shlo r);
    (parr + 8 * nch, if committed then 8 else 131072); (0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23) ].

(* [comment removed for export] *)
Definition art_sec_grant3 (HI t ctx parr spb l2 blk msz r : Z) : Prop :=
  art_sec_grant HI t ctx parr msz r
  /\ apart r msz spb (2 ^ 37 + 4096) /\ apart r msz l2 (2 ^ 20) /\ apart r msz blk (2 ^ 23).

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_allocate3_sec :
  forall (Q : list aev -> machine_state -> Prop) (P : Z -> Prop) (log : list aev) regs (M0 rom : word -> option byte) (raw : word)
         (sp HI n stk tp key tsd ctx t loff spb ris qs l2 blk trp szt rl rz qz rs qr qn m8 nd q msz nm parr nch : Z) (kb : nat) (committed : bool),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 1295832 ->
    getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
    (* [comment removed for export] *)
    8 <= n < 2 ^ 32 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 2 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> n <= rs <= n + 7 -> 65536 < rs + rz ->
    nd = rs + rz + rz -> 4096 * (q - 1) < nd <= 4096 * q -> msz = 4096 * q + 4096 ->
    (* [comment removed for export] *)
    art_geo HI t ctx tp tsd spb ris qs -> HI <= sp - 1952 -> HI + 4096 <= sp -> sp + 2144 <= 2 ^ 47 -> sp <= stk -> stk + 16 <= sp + 4096 ->
    0 <= trp < 2 ^ 64 -> 0 <= szt < 2 ^ 64 -> sp <= trp -> trp + 8 * szt <= sp + 4096 ->
    0 <= loff -> 0x10000 <= tp + loff -> tp + loff + 4 <= 0x696000 -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->
    l2 + 2 ^ 20 <= HI -> blk + 2 ^ 23 <= HI ->
    apart l2 (2 ^ 20) t 4096 -> apart l2 (2 ^ 20) ctx 4096 -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> 0x696000 <= l2 ->
    apart blk (2 ^ 23) t 4096 -> apart blk (2 ^ 23) ctx 4096 -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> 0x696000 <= blk ->
    0x696000 <= parr -> parr mod 4096 = 0 -> parr + 2 ^ 23 <= HI -> appmem parr (2 ^ 23) -> apart parr (2 ^ 23) t 4096 ->
    apart parr (2 ^ 23) ctx 4096 -> apart parr (2 ^ 23) l2 (2 ^ 20) -> apart parr (2 ^ 23) blk (2 ^ 23) ->
    0 <= nch < 16384 -> (committed = false -> nch = 0) -> 0x10000 <= nm < 2 ^ 47 ->
    (* [comment removed for export] *)
    wrA M0 (sp - 1952) 1952 -> wrA M0 t 4096 -> (committed = true -> wrA M0 parr 131072) ->
    art_alloc_rodata M0 -> art_rz_rodata M0 -> art_layout M0 -> art_tsd M0 tp key tsd ctx t -> art_prim_consts spb ris M0 ->
    cellA M0 0x140918 1 1 -> cellA M0 0x1c1ea2 1 0 -> cellA M0 (1295832 + 3616) 8 (2 ^ 40) -> cellA M0 (1295832 + 3624) 2 16 -> cellA M0 (1295832 + 3626) 2 2048 ->
    cellA M0 0x1d1700 8 0 -> cellA M0 (0x13d438 + 44) 4 4096 -> cellA M0 (0x13d438 + 52) 4 190 -> cellA M0 (0x13d438 + 85) 1 1 ->
    cellA M0 0x138120 8 loff -> cellA M0 (tp + loff) 4 0 -> cellA M0 t 8 ctx -> cellA M0 (ctx + 8) 4 0 ->
    cellA M0 stk 8 trp -> cellA M0 (stk + 8) 8 szt ->
    cellA M0 0x1374a8 8 0x139508 -> cellA M0 0x139508 8 nm ->
    cellA M0 0x13c618 8 4096 -> cellA M0 (0x13c618 + 8) 8 parr -> cellA M0 (0x13c618 + 16) 8 parr -> cellA M0 (0x13c618 + 56) 8 nch ->
    cellA M0 (0x13c618 + 48) 8 (if committed then 16384 else 0) -> cellA M0 (0x13c618 + 616) 4 0 ->
    (* [comment removed for export] *)
    (forall Mx r, GR log Mx msz r -> P r) -> (forall r, P r -> art_sec_grant3 HI t ctx parr spb l2 blk msz r) ->
    EVOK log (AMmapNull msz 0) ->
    (committed = false -> forall r, P r -> EVOK (log ++ [AMmapNull msz r]) (AMmapFixed (parr + 8 * nch) 131072)) ->
    (* [comment removed for export] *)
    DInvD l2 blk (S kb) M0 -> DPreD blk M0 trp szt -> DRoD M0 ->
    (forall r regs' (M' : word -> option byte) (b1 : Z), P r ->
        let ab := 4096 + r in
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 1 = raw ->
        (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
        mem_grows M0 M' -> art_agree (art_alloc3L_fp sp t parr nch r msz l2 blk committed) M0 M' ->
        (forall (x : word) b, art_shlo r <= U x < art_shhi r msz -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> M0 x = Some b -> M' x = Some b) ->
        DInvD l2 blk kb M' ->
        wrA M' r msz -> wrA M' (SB + r / 8) (msz / 8) ->
        cellA M' r 8 r -> cellA M' (r + 8) 8 msz -> cellA M' (r + 16) 8 nd -> cellA M' (r + 24) 8 nch ->
        0 <= b1 < 256 -> b1 mod 4 = 1 ->
        cellA M' (ab + rz - 16) 1 2 -> cellA M' (ab + rz - 15) 1 b1 -> cellA M' (ab + rz - 14) 2 0 -> cellA M' (ab + rz - 12) 4 n ->
        (forall j, 0 <= j < qn -> cellA M' (2147450880 + ab / 8 + 2 * qz + j) 1 0) -> (m8 <> 0 -> cellA M' (2147450880 + ab / 8 + 2 * qz + qn) 1 m8) ->
        cellA M' 0x13c618 8 4096 -> cellA M' (0x13c618 + 8) 8 parr -> cellA M' (0x13c618 + 16) 8 parr -> cellA M' (0x13c618 + 56) 8 (nch + 1) ->
        cellA M' (0x13c618 + 48) 8 16384 -> cellA M' (0x13c618 + 616) 4 0 ->
        cellA M' (parr + 8 * nch) 8 r -> wrA M' parr 131072 ->
        Q (log ++ art_sec_events msz r parr nch committed) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x525e4 : word) M0 rom).
Proof.
  intros Q P log regs M0 rom raw sp HI n stk tp key tsd ctx t loff spb ris qs l2 blk trp szt rl rz qz rs qr qn m8 nd q msz nm parr nch kb committed
         H1 Hret H2 H4 H10 H11 H12 H13 H14 H15
         Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz
         GEO HHI HHI' Hsp' Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd
         Dl2 Dblk Al2t Al2c Al2s Il2 Abt Abc Abs Iblk Hparr Hparr4 Hparr' APp Apt Apc Apl2 Apblk Hnch Hnch0 Hnm
         W Wt Wparr RO RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Ctrp Cszt Cnm1 Cnm2
         S0 S8 S16 S56 S48 S616 HGR HP EV1 EV2 DI DP DR K.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  assert (Ht2 : (4096 <= t /\ t + 4096 <= 0x10000) \/ 0x696000 <= t) by (clear - G7 G9; lia).
  assert (APt : appmem t 4096) by (unfold appmem, SB, kHighMemBeg; clear - G10; lia).
  assert (APc : appmem ctx 4096) by (unfold appmem, SB, kHighMemBeg; clear - G16; lia).
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in G15.
  change (hid ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x696000 <= t)) in Ht2.
  clear G10 G16.
  pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  (* [comment removed for export] *)
  assert (Hqr : (n + 7) / 8 = qr). { symmetry. apply (Z.div_unique _ 8 qr (n + 7 - 8 * qr)); lia. }
  assert (Ers_max : rs = (Z.max n 8 + 7) / 8 * 8) by (rewrite Z.max_l by lia; rewrite Hqr; lia).
  destruct (art_allocate_pre3a_sec regs M0 rom raw sp 1295832 n stk tp key tsd ctx t rl rs qr rz qz
              H1 H2 H4 H10 H11 H12 H13 H14 H15 ltac:(lia) Erl Erz Erz16 ltac:(lia)
              Ers_max Ers ltac:(rewrite Z.max_l by lia; lia) Hsec
              ltac:(lia) Hsp' Hstk Hstk' ltac:(lia) ltac:(lia)
              G7 ltac:(lia) G9 ltac:(unfold apart; lia) ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22
              W RO RZRO TSD Ci Cr Cmax Cmin16 Cmax2048)
    as (r5 & M5 & RUN5 & P5_1 & P5_2 & P5_4 & P5_8 & P5_9 & P5_10 & P5_11 & P5_12 & P5_13 & P5_19 & P5_20 & P5_21 & P5_22 & P5_23 & P5_25 & P5_26 & P5_27 & P5_3
        & G05 & AG05 & F120 & F112 & F104 & F96 & F88 & F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F8 & F16).
  eapply ar_steps; [exact RUN5|].
  assert (A05 : art_agree [(sp - 144, 144)] M0 M5). { intros x Hx. apply AG05. cbn in Hx. lia. }
  assert (GI0 : forall a n0, 0 <= n0 -> a + n0 <= sp - 144 -> art_gap [(sp - 144, 144)] a n0).
  { intros a n0 Hn0 Ha. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (T05 : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= sp - 144 -> cellA M0 a k v -> cellA M5 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M5 a k v A05); [|exact C]. split; [apply GI0; lia|lia]. }
  assert (Hnd8 : nd mod 8 = 0). { rewrite End, Ers, Erz16. replace (8 * qr + 16 * qz + 16 * qz) with ((qr + 4 * qz) * 8) by lia. apply Z_mod_mult. }
  (* [comment removed for export] *)
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
  assert (HP1 : forall r, P r -> art_sec_grant HI t ctx parr msz r) by (intros r Pr; exact (proj1 (HP r Pr))).
  assert (L5 : art_layout M5). { eapply art_layout_fp; [exact A05| |exact L]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
  assert (T5 : art_tsd M5 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A05| | |exact G19|exact G20|exact G21|exact G22|exact TSD].
    - intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
    - intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
  pose proof PC as (_ & _ & _ & _ & _ & Cg28 & Cpc & Cfb0 & C144).
  pose proof TSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  eapply (art_ca_sec_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) P log r5 M5 rom (0x52884 : bv 64)%bv (sp - 128) HI nd q msz nm tp key tsd ctx t parr nch committed
            P5_1 ltac:(unfold ret_ok; bveq) P5_2 P5_4 P5_10 ltac:(rewrite P5_12; f_equal; lia) P5_13
            ltac:(clear - Hsec End Hrs Hn Hqz Erz16; lia) Hnd8 Hq Emsz ltac:(unfold kHighMemBeg; clear - G1; lia) ltac:(clear - HHI; lia) ltac:(clear - Hsp'; lia)
            Ht2 G8 APt G13 G14 APc G18 ltac:(clear - Htpd; lia) ltac:(clear - G20; lia) ltac:(clear - G21; lia) ltac:(clear - G22 Hkey; lia)
            Hparr Hparr4 Hparr' APp Apt Hnch Hnch0 Hnm
            ltac:(eapply wr_grows; [exact G05|]; eapply wr_sub; [exact W|lia|lia]) ltac:(eapply wr_grows; [exact G05|exact Wt])
            ltac:(intros E; eapply wr_grows; [exact G05|exact (Wparr E)])
            ltac:(apply T05; [lia|cbn; lia|exact Cg28]) ltac:(apply T05; [lia|cbn; lia|exact Cpc]) ltac:(apply T05; [lia|cbn; lia|exact Cfb0]) ltac:(apply T05; [lia|cbn; lia|exact C144])
            ltac:(apply T05; [lia|cbn; lia|exact Cnm1]) ltac:(apply T05; [lia|cbn; lia|exact Cnm2]) L5 T5
            ltac:(apply T05; [lia|cbn; lia|exact S0]) ltac:(apply T05; [lia|cbn; lia|exact S8]) ltac:(apply T05; [lia|cbn; lia|exact S16]) ltac:(apply T05; [lia|cbn; lia|exact S56])
            ltac:(apply T05; [lia|cbn; lia|exact S48]) ltac:(apply T05; [lia|cbn; lia|exact S616])
            HGR HP1 EV1 EV2).
  intros r r6 M6 Pr R10 R2 R1 RK G56 A56 WIN WSr WSs Cr0 Cr8 Cr16 Cr24 ZB SS0 SS8 SS16 SS56 SS48 SS616 Sslot WSp.
  destruct (HP r Pr) as ((Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp) & Ark & Arl2 & Arblk).
  (* [comment removed for export] *)
  assert (Hm4 : msz mod 4096 = 0). { rewrite Emsz. replace (4096 * q + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
  assert (Hq1 : 17 <= q) by (clear - Hq Hsec End Hqz Erz16; lia).
  destruct (art_sh_bounds r msz Hr4 Hm4 ltac:(lia) ltac:(lia) ltac:(clear - Hrm G2; lia)) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7).
  unfold SB, kHighMemBeg in SH1, SH2, SH3, SH4.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  set (ab := 4096 + r) in *.
  assert (Eab : ab = 4096 + r) by reflexivity. clearbody ab.
  assert (Hab4 : ab mod 4096 = 0). { rewrite Eab. rewrite Z.add_mod, Hr4 by lia. reflexivity. }
  assert (Hab16 : ab mod 16 = 0).
  { pose proof (Z.div_mod ab 4096 ltac:(lia)) as E. rewrite Hab4 in E. rewrite E. replace (4096 * (ab / 4096) + 0) with (256 * (ab / 4096) * 16) by lia. apply Z_mod_mult. }
  assert (Hrz16 : rz mod 16 = 0). { rewrite Erz16, Z.mul_comm. apply Z_mod_mult. }
  assert (Hab8d : ab / 8 = r / 8 + 512). { rewrite Eab. replace (4096 + r) with (r + 512 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hmsz8 : msz / 8 = 512 * q + 512). { rewrite Emsz. replace (4096 * q + 4096) with ((512 * q + 512) * 8) by lia. apply Z.div_mul. lia. }
  unfold appmem, SB, kHighMemBeg in APr.
  change (hid (r + msz <= 2147450880 - 4096 \/ 0x10007fff8000 <= r)) in APr.
  (* [comment removed for export] *)
  #[local] Ltac zone_tac := unfold art_ca_sec_fp, art_sec_fp; unfold hid, apart in *; cbn [art_gap app fst snd]; unfold apart;
                            lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => idtac end; repeat split; try exact I; lia.
  assert (Z56i : forall a n0, 0 <= n0 -> (0x10000 <= a /\ a + n0 <= 0x13c618) \/ (0x13c8a8 <= a /\ a + n0 <= 0x696000) ->
                   art_gap (art_ca_sec_fp (sp - 128) t parr nch r msz committed) a n0).
  { intros a n0 Hn0 Z. fold lo hi. clear - Hn0 Z G1 HHI G9 Hri SH1 Hparr Hnch. zone_tac. }
  assert (Z56f : forall a n0, 0 <= n0 -> sp - 128 <= a -> a + n0 <= sp + 4096 -> art_gap (art_ca_sec_fp (sp - 128) t parr nch r msz committed) a n0).
  { intros a n0 Hn0 Z Z'. fold lo hi. clear - Hn0 Z Z' G1 HHI G8 Hrm SH4 Hparr' Hnch. zone_tac. }
  assert (Z56t : forall a n0, 0 <= n0 -> (t <= a /\ a + n0 <= t + 2872) \/ (t + 2888 <= a /\ a + n0 <= t + 4096) -> art_gap (art_ca_sec_fp (sp - 128) t parr nch r msz committed) a n0).
  { intros a n0 Hn0 Z. fold lo hi. clear - Hn0 Z G1 HHI G7 G8 G9 Art At_s SH1 SH4 Apt Hnch. zone_tac. }
  assert (Z56c : forall a n0, 0 <= n0 -> ctx <= a -> a + n0 <= ctx + 4096 -> art_gap (art_ca_sec_fp (sp - 128) t parr nch r msz committed) a n0).
  { intros a n0 Hn0 Z Z'. fold lo hi. clear - Hn0 Z Z' G1 HHI G13 G14 G15 G18 Arc Ac_s SH1 SH4 Apc Hnch. zone_tac. }
  assert (Z56d : forall a n0, 0 <= n0 -> (l2 <= a /\ a + n0 <= l2 + 2 ^ 20) \/ (blk <= a /\ a + n0 <= blk + 2 ^ 23) -> art_gap (art_ca_sec_fp (sp - 128) t parr nch r msz committed) a n0).
  { intros a n0 Hn0 Z. fold lo hi. clear - Hn0 Z G1 HHI Dl2 Dblk Il2 Iblk Al2t Abt Arl2 Arblk Al2s Abs SH1 SH4 Apl2 Apblk Hnch. zone_tac. }
  assert (T56 : forall a (k : nat) v, art_gap (art_ca_sec_fp (sp - 128) t parr nch r msz committed) a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M5 a k v -> cellA M6 a k v).
  { intros a k v Gp Ha Hk C. exact (art_cell_tr _ M5 M6 a k v A56 Gp Ha Hk C). }
  (* [comment removed for export] *)
  assert (Hrzb : 32 <= rz <= 2048) by (clear - Hqz Erz16; lia).
  assert (Hn4 : 4096 <= n) by (clear - Hsec Hrs Hrzb; lia).
  assert (Cob : cellA M6 (ab + rz - 15) 1 0). { apply art_cell1_of_byte; [lia|]. apply ZB. rewrite art_u_lit by (clear - Eab Hr Hrm G2 Hrzb Hq1 Emsz; lia). clear - Eab Hrzb Hq1 Emsz. lia. }
  assert (R6_10 : getr r6 10 = Z_to_bv 64 ab) by exact R10.
  assert (R6_9 : getr r6 9 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_9).
  assert (R6_19 : getr r6 19 = Z_to_bv 64 (rs + rz + rz)) by (rewrite RK by inl; exact P5_19).
  assert (R6_20 : getr r6 20 = Z_to_bv 64 rz) by (rewrite RK by inl; exact P5_20).
  assert (R6_21 : getr r6 21 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_21).
  assert (R6_22 : getr r6 22 = Z_to_bv 64 1295832) by (rewrite RK by inl; exact P5_22).
  assert (R6_23 : getr r6 23 = Z_to_bv 64 stk) by (rewrite RK by inl; exact P5_23).
  assert (R6_25 : getr r6 25 = Z_to_bv 64 7) by (rewrite RK by inl; exact P5_25).
  assert (R6_26 : getr r6 26 = Z_to_bv 64 t) by (rewrite RK by inl; exact P5_26).
  assert (R6_27 : getr r6 27 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_27).
  assert (R6_4 : getr r6 4 = Z_to_bv 64 tp) by (rewrite RK by inl; exact P5_4).
  assert (R6_8 : getr r6 8 = Z_to_bv 64 0) by (rewrite RK by inl; exact P5_8).
  assert (R6_3 : getr r6 3 = getr regs 3) by (rewrite RK by inl; exact P5_3).
  assert (F16_6 : cellA M6 (sp - 128 + 16) 8 16) by (apply T56; [apply Z56f; clear; cbn; lia|clear - G1 HHI; lia|clear - Hsp'; cbn; lia|exact F16]).
  assert (Ctctx6 : cellA M6 t 8 ctx) by (apply T56; [apply Z56t; clear; cbn; lia|clear - G7; lia|clear - G8 G2; cbn; lia|apply T05; [clear - G7; lia|clear - G8 HHI; cbn; lia|exact Ctctx]]).
  assert (Ctid6 : cellA M6 (ctx + 8) 4 0) by (apply T56; [apply Z56c; clear; cbn; lia|clear - G13; lia|clear - G14 G2; cbn; lia|apply T05; [clear - G13; lia|clear - G14 HHI; cbn; lia|exact Ctid]]).
  assert (GS0 : forall a n0, 0 <= n0 -> sp <= a -> art_gap [(sp - 144, 144)] a n0) by (intros a n0 Hn0 Ha; cbn [art_gap fst snd]; unfold apart; repeat split; try exact I; lia).
  assert (Ctrp6 : cellA M6 stk 8 trp).
  { apply T56; [apply Z56f; clear - Hstk Hstk'; cbn; lia|clear - Hstk G1 HHI; lia|clear - Hstk' Hsp'; cbn; lia|].
    apply (art_cell_tr1 _ M0 M5 _ _ _ A05); [|exact Ctrp]. split; [apply GS0; [clear; cbn; lia|exact Hstk]|clear - Hstk Hstk' G1 HHI Hsp'; cbn; lia]. }
  assert (Cszt6 : cellA M6 (stk + 8) 8 szt).
  { apply T56; [apply Z56f; clear - Hstk Hstk'; cbn; lia|clear - Hstk G1 HHI; lia|clear - Hstk' Hsp'; cbn; lia|].
    apply (art_cell_tr1 _ M0 M5 _ _ _ A05); [|exact Cszt]. split; [apply GS0; [clear; cbn; lia|clear - Hstk; lia]|clear - Hstk Hstk' G1 HHI Hsp'; cbn; lia]. }
  assert (Hblk : ab + rs + rz + rz <= r + msz) by (clear - Eab End Hq Emsz; lia).
  pose proof (art_alloc_b_sec_fn r6 M6 rom (sp - 128) ab n rs rz stk t ctx 0 trp szt R2 R6_10 R6_9 R6_19 R6_20 R6_21 R6_23 R6_25 R6_26 R6_27
                ltac:(clear - G1 HHI; lia) ltac:(clear - Hsp'; lia) ltac:(clear - Eab Hr; lia) ltac:(clear - Hblk Hrm G2; lia) Hab16 ltac:(clear - Hn; lia) Ers_max ltac:(clear - Hrzb; lia) Hrz16 ltac:(clear - Hn Hrs Hrzb; lia)
                ltac:(clear - Hstk G1 HHI; lia) ltac:(clear - Hstk' Hsp'; lia) G7 ltac:(clear - G8 G2; lia) G13 ltac:(clear - G14 G2; lia) ltac:(clear; lia) Htrp Hszt
                ltac:(eapply wr_sub; [exact WSr|clear - Eab Hrzb; lia|clear - Hblk Hrs Hn Hrzb; lia])
                Cob F16_6 Ctctx6 Ctid6 Ctrp6 Cszt6
                ltac:(clear - Hblk Hrm HHI Hrs Hn Hrzb; unfold apart; lia) ltac:(clear - Art Eab Hrzb Hblk Hrs Hn; unfold apart in *; lia)
                ltac:(clear - Arc Eab Hrzb Hblk Hrs Hn; unfold apart in *; lia) ltac:(clear - Hblk Hrm HHI Hstk Hrs Hn Hrzb; unfold apart; lia)) as RUN7.
  match type of RUN7 with msteps _ _ (mkst ?R _ ?MM _) => set (R7 := R) in RUN7; set (M7 := MM) in RUN7 end.
  eapply ar_steps; [exact RUN7|].
  assert (A67 : art_agree [(ab + rz - 16, 16)] M6 M7).
  { unfold M7, art_alloc_memB. clear - Eab Hr Hrm G2 Hrzb Hblk Hrs Hn. eapply art_agree_sub; [zagree|]. zsub_c ltac:(clear). }
  assert (G67 : mem_grows M6 M7) by (unfold M7, art_alloc_memB; zgrows).
  assert (Hn32 : n / 2 ^ 32 = 0) by (apply Z.div_small; clear - Hn; lia).
  pose proof (art_hdr_b1a_range 0 ltac:(lia)) as Hb1a. pose proof (art_hdr_b1_range 0 ltac:(lia)) as Hb1.
  assert (B7 : cellA M7 (ab + rz - 15) 1 (art_hdr_b1 0) /\ cellA M7 (ab + rz - 12) 4 n /\ cellA M7 (ab + rz - 14) 2 0).
  { unfold M7, art_alloc_memB. rewrite Hn32. clear - Hb1a Hb1 Eab Hr Hrm G2 Hrzb Hblk Hrs Hn. repeat split; zcell. }
  destruct B7 as (B7a & B7b & B7c).
  (* [comment removed for export] *)
  assert (AGD : forall x : word, dprivD l2 blk (U x) -> M7 x = M0 x).
  { intros x Dx.
    assert (O1 : art_out [(ab + rz - 16, 16)] (U x)).
    { unfold dprivD in Dx. clear - Dx Eab Hri Hrzb Hblk Hrs Hn Arl2 Arblk. unfold apart in *. cbn [art_out fst snd]. repeat split; try exact I; lia. }
    assert (O2 : art_out (art_ca_sec_fp (sp - 128) t parr nch r msz committed) (U x)).
    { unfold dprivD in Dx. destruct Dx as [D|D].
      - eapply art_gap_out; [apply (Z56i 0x211b08 (0x661b28 - 0x211b08)); lia|lia].
      - destruct D as [D|D]; [eapply art_gap_out; [apply (Z56d l2 (2 ^ 20)); lia|lia] | eapply art_gap_out; [apply (Z56d blk (2 ^ 23)); lia|lia]]. }
    assert (O3 : art_out [(sp - 144, 144)] (U x)).
    { unfold dprivD in Dx. clear - Dx HHI G1 Dl2 Dblk. cbn [art_out fst snd]. repeat split; try exact I; lia. }
    rewrite (A67 x O1), (A56 x O2), (A05 x O3). reflexivity. }
  assert (DI7 : DInvD l2 blk (S kb) M7) by (apply (DInvD_frame l2 blk (S kb) M0 M7 DI); exact AGD).
  assert (DP7 : DPreD blk M7 trp szt).
  { apply (DPreD_frame blk M0 M7 trp szt DP). intros x Hx.
    rewrite (A67 x), (A56 x), (A05 x); [reflexivity| | |].
    - clear - Hx Htrp1. cbn [art_out fst snd]. repeat split; try exact I; lia.
    - eapply art_gap_out; [apply (Z56f trp (8 * szt)); clear - Htrp1 Htrp2 Hszt; lia|exact Hx].
    - clear - Hx Htrp1 Hblk Hrm HHI Hrs Hn Hrzb. cbn [art_out fst snd]. repeat split; try exact I; lia. }
  assert (T07i : forall a (k : nat) v, (0x10000 <= a /\ a + Z.of_nat k <= 0x13c618) \/ (0x13c8a8 <= a /\ a + Z.of_nat k <= 0x696000) -> cellA M0 a k v -> cellA M7 a k v).
  { intros a k v Z C. apply (art_cell_tr1 _ M6 M7 a k v A67); [|apply T56; [apply Z56i; lia|lia|lia|apply T05; [lia|clear - Z HHI G1; lia|exact C]]].
    clear - Z Eab Hri Hrzb. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (DR7 : DRoD M7). { destruct DR as (D1 & D2 & D3). unfold DRoD. repeat split; (apply T07i; [left; cbn; lia|assumption]). }
  assert (G07 : mem_grows M0 M7) by (eapply mem_grows_trans; [exact G05|]; eapply mem_grows_trans; [exact G56|exact G67]).
  assert (W7 : wrA M7 (sp - 128 - 224) 224) by (eapply wr_grows; [exact G07|]; eapply wr_sub; [exact W|lia|lia]).
  assert (ND7 : nodp (dprivD l2 blk) (sp - 128 - 224) 224). { intros i Hi D. unfold dprivD in D. clear - Hi D HHI G1 Dl2 Dblk. lia. }
  pose proof (art_depot_spec_holds l2 blk) as DEPOT. unfold art_depot_spec in DEPOT.
  destruct (DEPOT kb R7 M7 rom (0x52990 : bv 64)%bv (sp - 128) trp szt ltac:(unfold R7; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold R7; gres; exact R2)
              ltac:(unfold R7; gres; reflexivity) ltac:(unfold R7; gres; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) W7 ND7 DI7 DP7 DR7)
    as (r8 & M8 & id & RUN8 & P8_10 & Hid & K8 & G78 & AGd & DI8).
  clear DEPOT.
  eapply ar_steps; [exact RUN8|].
  assert (A78 : art_agree [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)] M7 M8).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply AGd; [unfold dprivD; clear - Hx; lia | clear - Hx; lia]. }
  (* [comment removed for export] *)
  assert (A68 : art_agree ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) M6 M8)
    by (exact (art_agree_trans _ _ _ _ _ A67 A78)).
  #[local] Ltac zone2_tac := unfold hid, apart in *; cbn [art_gap app fst snd]; unfold apart; repeat split; try exact I; lia.
  assert (Z68i : forall a n0, 0 <= n0 -> (0x10000 <= a /\ a + n0 <= 0x211b08) \/ (0x661b28 <= a /\ a + n0 <= 0x696000) ->
                   art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a n0).
  { intros a n0 Hn0 Z. clear - Hn0 Z G1 HHI Hri Eab Hrzb Il2 Iblk. zone2_tac. }
  assert (Z68f : forall a n0, 0 <= n0 -> sp - 128 <= a -> a + n0 <= sp + 4096 ->
                   art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a n0).
  { intros a n0 Hn0 Z Z'. clear - Hn0 Z Z' G1 HHI Hblk Hrm Hrs Hn Hrzb Dl2 Dblk. zone2_tac. }
  assert (Z68t : forall a n0, 0 <= n0 -> t <= a -> a + n0 <= t + 4096 ->
                   art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a n0).
  { intros a n0 Hn0 Z Z'. clear - Hn0 Z Z' G1 HHI G7 G8 G9 Art Eab Hrzb Hblk Hrs Hn Al2t Abt. zone2_tac. }
  assert (Z68c : forall a n0, 0 <= n0 -> ctx <= a -> a + n0 <= ctx + 4096 ->
                   art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a n0).
  { intros a n0 Hn0 Z Z'. clear - Hn0 Z Z' G1 HHI G13 G14 G15 Arc Eab Hrzb Hblk Hrs Hn Al2c Abc. zone2_tac. }
  assert (Z68b : forall a n0, 0 <= n0 -> (r <= a /\ a + n0 <= ab + rz - 16) \/ (ab + rz <= a /\ a + n0 <= r + msz) ->
                   art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a n0).
  { intros a n0 Hn0 Z. clear - Hn0 Z G1 HHI Hri Hrm Arl2 Arblk Eab Hrzb Hblk Hrs Hn. zone2_tac. }
  assert (Z68p : forall a n0, 0 <= n0 -> parr <= a -> a + n0 <= parr + 2 ^ 23 ->
                   art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a n0).
  { intros a n0 Hn0 Z Z'. clear - Hn0 Z Z' G1 HHI Hparr Hparr' Arp Eab Hrzb Hblk Hrs Hn Apl2 Apblk. zone2_tac. }
  assert (T68 : forall a (k : nat) v, art_gap ([(ab + rz - 16, 16)] ++ [(0x211b08, 0x661b28 - 0x211b08); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)]) a (Z.of_nat k) ->
                  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M6 a k v -> cellA M8 a k v).
  { intros a k v Gp Ha Hk C. exact (art_cell_tr _ M6 M8 a k v A68 Gp Ha Hk C). }
  assert (T08i : forall a (k : nat) v, (0x10000 <= a /\ a + Z.of_nat k <= 0x13c618) \/ (0x13c8a8 <= a /\ a + Z.of_nat k <= 0x211b08) \/ (0x661b28 <= a /\ a + Z.of_nat k <= 0x696000) ->
                  cellA M0 a k v -> cellA M8 a k v).
  { intros a k v Z C. apply T68; [apply Z68i; lia|lia|lia|]. apply T56; [apply Z56i; lia|lia|lia|]. apply T05; [lia|clear - Z HHI G1; lia|exact C]. }
  assert (T58f : forall a (k : nat) v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M5 a k v -> cellA M8 a k v).
  { intros a k v Ha Hk C. apply T68; [apply Z68f; lia|clear - Ha G1 HHI; lia|clear - Hk Hsp'; lia|]. apply T56; [apply Z56f; lia|clear - Ha G1 HHI; lia|clear - Hk Hsp'; lia|exact C]. }
  assert (G08 : mem_grows M0 M8) by (eapply mem_grows_trans; [exact G07|exact G78]).
  assert (G68 : mem_grows M6 M8) by (eapply mem_grows_trans; [exact G67|exact G78]).
  assert (W8 : wrA M8 (sp - 1952) 1952) by (eapply wr_grows; [exact G08|exact W]).
  assert (Wab8 : wrA M8 ab (4096 * q)) by (eapply wr_grows; [exact G68|]; eapply wr_sub; [exact WSr|clear - Eab; lia|clear - Eab Emsz; lia]).
  assert (Wsh8 : wrA M8 (2147450880 + ab / 8) (512 * q)).
  { eapply wr_grows; [exact G68|]. eapply wr_sub; [exact WSs|unfold SB; clear - Hab8d; lia|unfold SB; clear - Hab8d Hmsz8; lia]. }
  assert (Wt8 : wrA M8 t 4096) by (eapply wr_grows; [exact G08|exact Wt]).
  assert (L8 : art_layout M8).
  { unfold art_layout in *. decompose [and] L. zsplit;
      (apply T08i; [first [left; cbn; (clear - hi lo msz r; lia) | right; left; cbn; (clear - hi lo msz r; lia)]|assumption]). }
  assert (T8 : art_tsd M8 tp key tsd ctx t).
  { destruct TSD as (C1 & C2 & C3 & C4 & C5 & RR). unfold art_tsd. split; [|split; [|split; [|split; [|split; [|exact RR]]]]].
    - apply T08i; [right; left; cbn; lia|exact C1].
    - apply T08i; [right; left; cbn; lia|exact C2].
    - apply T08i; [right; right; clear - Htpd G20; cbn; lia|exact C3].
    - apply T08i; [right; right; clear - Htsdd G22 Hkey; cbn; lia|exact C4].
    - apply T68; [apply Z68c; clear; cbn; lia|clear - G13; lia|clear - G14 G2; cbn; lia|]. apply T56; [apply Z56c; clear; cbn; lia|clear - G13; lia|clear - G14 G2; cbn; lia|].
      apply T05; [clear - G13; lia|clear - G14 HHI; cbn; lia|exact C5]. }
  assert (RO3 : cellA M0 0x10360 8 0xcc6e96b9cc6e96b9) by (unfold art_alloc_rodata in RO; tauto).
  pose proof PC as (Cspb & _).
  assert (B8a : cellA M8 (ab + rz - 15) 1 (art_hdr_b1 0)). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7a]. clear - G1 G2 HHI Hri Hrm Eab Hrzb Hblk Hrs Hn Arl2 Arblk. split; [zone2_tac|cbn; lia]. }
  assert (B8b : cellA M8 (ab + rz - 12) 4 n). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7b]. clear - G1 G2 HHI Hri Hrm Eab Hrzb Hblk Hrs Hn Arl2 Arblk. split; [zone2_tac|cbn; lia]. }
  assert (B8c : cellA M8 (ab + rz - 14) 2 0). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7c]. clear - G1 G2 HHI Hri Hrm Eab Hrzb Hblk Hrs Hn Arl2 Arblk. split; [zone2_tac|cbn; lia]. }
  assert (R8_2 : getr r8 2 = Z_to_bv 64 (sp - 128)) by (rewrite K8 by dk8; unfold R7; gres; exact R2).
  assert (R8_3 : getr r8 3 = getr regs 3) by (rewrite K8 by dk8; unfold R7; gres; exact R6_3).
  assert (R8_4 : getr r8 4 = Z_to_bv 64 tp) by (rewrite K8 by dk8; unfold R7; gres; exact R6_4).
  assert (R8_8 : getr r8 8 = Z_to_bv 64 0) by (rewrite K8 by dk8; unfold R7; gres; exact R6_8).
  assert (R8_9 : getr r8 9 = Z_to_bv 64 n) by (rewrite K8 by dk8; unfold R7; gres; exact R6_9).
  assert (R8_18 : getr r8 18 = Z_to_bv 64 ab) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_19 : getr r8 19 = Z_to_bv 64 nd) by (rewrite K8 by dk8; unfold R7; gres; rewrite R6_19; f_equal; clear - End; lia).
  assert (R8_20 : getr r8 20 = Z_to_bv 64 (ab + rz)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_21 : getr r8 21 = Z_to_bv 64 (ab + rz - 16)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_22 : getr r8 22 = Z_to_bv 64 1295832) by (rewrite K8 by dk8; unfold R7; gres; exact R6_22).
  assert (R8_24 : getr r8 24 = Z_to_bv 64 0) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  assert (R8_25 : getr r8 25 = Z_to_bv 64 (ab + rz + n)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
  (* [comment removed for export] *)
  assert (Hspbhi : spb + 2 ^ 37 < 2 ^ 48) by (clear - Eris G6 G2; lia).
  destruct (art_allocate_post_sec r8 M8 rom raw sp n qn m8 rs qr rz qz nd q ab spb t tp loff key tsd ctx id (art_hdr_b1 0)
              (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
              (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25)) (U (getr regs 26)) (U (getr regs 27))
              eq_refl Hret R8_2 R8_4 R8_8 R8_9 P8_10 R8_18 R8_19 R8_20 R8_21 R8_22 R8_24 R8_25
              ltac:(clear - Hn4 Hn; lia) En Hm8 Ers Hrs Erz16 Hrzb End ltac:(clear - Hsec End Hrzb; lia) Hq
              ltac:(clear - G1 HHI'; lia) Hsp'
              G7 ltac:(clear - G8 G2; lia) G9 ltac:(clear - G8 HHI; unfold apart; lia) ltac:(clear - At_s; unfold apart in *; lia)
              ltac:(clear - G14 HHI; unfold apart; lia) G15 G18 ltac:(clear - Ac_s; unfold apart in *; lia)
              Hloff G19 G20 Hloff' Hloff'' G21 G22
              Hab4 ltac:(clear - Eab Hri; lia) ltac:(clear - APr Eab Emsz; unfold hid in APr; lia) ltac:(clear - Eab Emsz Hrm G2; lia)
              ltac:(clear - Eab Emsz Hrm HHI; unfold apart; lia) ltac:(clear - Art Eab Emsz; unfold apart in *; lia) ltac:(clear - Arc Eab Emsz; unfold apart in *; lia)
              ltac:(clear - G4; lia) Hspbhi ltac:(clear - Ark Eab Emsz Hq1; unfold apart in Ark; lia)
              Hid Hb1
              (u64_range raw) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
              W8 Wab8 Wsh8 Wt8 L8 T8
              ltac:(apply T08i; [left; clear; cbn; lia|exact Cspb])
              ltac:(apply T68; [apply Z68i; clear; cbn; lia|clear; lia|clear; cbn; lia|exact SS0])
              ltac:(replace (ab - 4096 + 16) with (r + 16) by (clear - Eab; lia); apply T68; [apply Z68b; [clear; cbn; lia|left; clear - Eab Hrzb; cbn; lia]|clear - Hr; lia|clear - Hrm G2 Hq1 Emsz; cbn; lia|exact Cr16])
              ltac:(apply T08i; [right; left; clear; cbn; lia|exact Cpp]) ltac:(apply T08i; [right; left; clear; cbn; lia|exact Cmfs]) ltac:(apply T08i; [right; left; clear; cbn; lia|exact Cfb])
              ltac:(apply T08i; [left; clear; cbn; lia|exact Cg]) ltac:(apply T08i; [right; right; clear - Htpd Hloff Hloff''; cbn; lia|exact Clsan])
              ltac:(apply T08i; [right; left; clear; cbn; lia|exact Chook]) ltac:(apply T08i; [left; clear; cbn; lia|exact RO3])
              B8a B8b B8c
              ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F8])
              ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F120]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F112]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F104])
              ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F96]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F88]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F80])
              ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F72]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F64]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F56])
              ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F48]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F40]) ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F32])
              ltac:(apply T58f; [clear; lia|clear; cbn; lia|exact F24]))
    as (rF & MF & RUNF & PF10 & PF2 & PF1 & PF8 & PF9 & PF18 & PF19 & PF20 & PF21 & PF22 & PF23 & PF24 & PF25 & PF26 & PF27 & GF & A8F & CL1 & CL2 & CL3 & CL4 & CLid & CLmag & CLcb & SHZ & SHP & PF3 & PF4).
  eapply ar_steps; [exact RUNF|]. apply ar_done.
  (* [comment removed for export] *)
  assert (Z8Fi : forall a n0, 0 <= n0 -> 0x10000 <= a -> a + n0 <= 0x696000 -> art_gap (art_postL_fp sp t ab rz q) a n0).
  { intros a n0 Hn0 Z Z'. unfold art_postL_fp. rewrite Hab8d. clear - Hn0 Z Z' G1 HHI G9 Hri Eab Hrzb SH6 Hr. zone2_tac. }
  assert (Z8Fb : forall a n0, 0 <= n0 -> r <= a -> a + n0 <= ab -> art_gap (art_postL_fp sp t ab rz q) a n0).
  { intros a n0 Hn0 Z Z'. unfold art_postL_fp. rewrite Hab8d. clear - Hn0 Z Z' G1 HHI Hrm Art APr Eab Hrzb SH6 Hr Hq1 Emsz Hmsz8 SH7 G2. zone2_tac. }
  assert (Z8Fp : forall a n0, 0 <= n0 -> parr <= a -> a + n0 <= parr + 2 ^ 23 -> art_gap (art_postL_fp sp t ab rz q) a n0).
  { intros a n0 Hn0 Z Z'. unfold art_postL_fp. rewrite Hab8d. unfold appmem, SB, kHighMemBeg in APp. clear - Hn0 Z Z' G1 HHI Hparr' Arp Apt APp Eab Hrzb Hblk Hrs Hn4 SH6 Hr Hq1 Emsz Hmsz8 SH7 Hrm G2. zone2_tac. }
  assert (Z8Fd : forall a n0, 0 <= n0 -> (0x211b08 <= a /\ a + n0 <= 0x661b28) \/ (l2 <= a /\ a + n0 <= l2 + 2 ^ 20) \/ (blk <= a /\ a + n0 <= blk + 2 ^ 23) -> art_gap (art_postL_fp sp t ab rz q) a n0).
  { intros a n0 Hn0 Z. unfold art_postL_fp. rewrite Hab8d. clear - Hn0 Z G1 HHI G9 Hri Dl2 Dblk Il2 Iblk Al2t Abt Al2s Abs Arl2 Arblk Eab Hrzb Hblk Hrs Hn4 SH6 Hr Hq1 Emsz Hmsz8 SH7 Hrm G2. zone2_tac. }
  assert (T8F : forall a (k : nat) v, art_gap (art_postL_fp sp t ab rz q) a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M8 a k v -> cellA MF a k v).
  { intros a k v Gp Ha Hk C. exact (art_cell_tr _ M8 MF a k v A8F Gp Ha Hk C). }
  assert (G6F : mem_grows M6 MF) by (eapply mem_grows_trans; [exact G68|exact GF]).
  pose proof (art_hdr_b1_type 0 ltac:(lia)) as (Hty & Hb1').
  assert (Hr47 : r + msz < 2 ^ 47) by (clear - Hrm G2; lia).
  subst ab.
  apply (K r rF MF (Z.land (art_hdr_b1 0) 243) Pr).
  - exact PF10.
  - exact PF2.
  - exact PF1.
  - intros x Hx. cbn [In] in Hx.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      [ rewrite PF3; exact R8_3 | rewrite PF4, R8_4; symmetry; exact H4
      | rewrite PF8 | rewrite PF9 | rewrite PF18 | rewrite PF19 | rewrite PF20 | rewrite PF21 | rewrite PF22 | rewrite PF23 | rewrite PF24 | rewrite PF25 | rewrite PF26 | rewrite PF27 ];
      apply Z_to_bv_bv_unsigned.
  - eapply mem_grows_trans; [exact G08|exact GF].
  - eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A05 (art_agree_trans _ _ _ _ _ A56 (art_agree_trans _ _ _ _ _ A68 A8F)))|].
    unfold art_alloc3L_fp, art_ca_sec_fp, art_sec_fp, art_postL_fp. fold lo hi. rewrite Hab8d. intros z.
    clear - SH2 SH3 Hmsz8 Hrzb Hblk Hn4 Hrs Hq1 Emsz. intros Hz H. cbn [art_out app fst snd] in H |- *. destruct committed; repeat split; try exact I; lia.
  - intros x b Hx Nx Mx. pose proof (bv_unsigned_in_range 64 x) as Rx.
    rewrite (art_agree_pt _ _ _ x A8F).
    2:{ unfold art_postL_fp. rewrite Hab8d. unfold hid in APr. unfold SB in Nx. clear - Hx Nx SH1 SH4 G1 HHI APr At_s Hmsz8 Hrzb Hblk Hn4 Hrs Hq1 Emsz. unfold apart in *. cbn [art_out fst snd]. repeat split; try exact I; lia. }
    rewrite (art_agree_pt _ _ _ x A68).
    2:{ unfold hid in APr. clear - Hx SH1 SH4 G1 HHI APr Al2s Abs Hrzb Hblk Hn4 Hrs Hq1 Emsz. unfold apart in *. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
    apply (WIN x b Hx Nx). rewrite (art_agree_pt _ _ _ x A05); [exact Mx|]. clear - Hx SH4 G1 HHI. cbn [art_out fst snd]. repeat split; try exact I; lia.
  - apply (DInvD_frame l2 blk kb M8 MF DI8). intros x Dx. apply A8F. unfold dprivD in Dx. eapply art_gap_out; [apply (Z8Fd (U x) 1); [lia|clear - Dx; lia]|lia].
  - eapply wr_grows; [exact G6F|exact WSr].
  - eapply wr_grows; [exact G6F|exact WSs].
  - apply T8F; [apply Z8Fb; clear; cbn; lia|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|]. apply T68; [apply Z68b; [clear; cbn; lia|left; clear - Hrzb; cbn; lia]|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|exact Cr0].
  - apply T8F; [apply Z8Fb; clear; cbn; lia|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|]. apply T68; [apply Z68b; [clear; cbn; lia|left; clear - Hrzb; cbn; lia]|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|exact Cr8].
  - apply T8F; [apply Z8Fb; clear; cbn; lia|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|]. apply T68; [apply Z68b; [clear; cbn; lia|left; clear - Hrzb; cbn; lia]|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|exact Cr16].
  - apply T8F; [apply Z8Fb; clear; cbn; lia|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|]. apply T68; [apply Z68b; [clear; cbn; lia|left; clear - Hrzb; cbn; lia]|clear - Hr; lia|clear - Hr47 Hq1 Emsz; cbn; lia|exact Cr24].
  - exact Hb1'.
  - exact Hty.
  - exact CL1.
  - exact CL3.
  - exact CL4.
  - exact CL2.
  - exact SHZ.
  - exact SHP.
  - apply T8F; [apply Z8Fi; clear; cbn; lia|clear; lia|clear; cbn; lia|]. apply T68; [apply Z68i; [clear; cbn; lia|left; clear; cbn; lia]|clear; lia|clear; cbn; lia|exact SS0].
  - apply T8F; [apply Z8Fi; clear; cbn; lia|clear; lia|clear; cbn; lia|]. apply T68; [apply Z68i; [clear; cbn; lia|left; clear; cbn; lia]|clear; lia|clear; cbn; lia|exact SS8].
  - apply T8F; [apply Z8Fi; clear; cbn; lia|clear; lia|clear; cbn; lia|]. apply T68; [apply Z68i; [clear; cbn; lia|left; clear; cbn; lia]|clear; lia|clear; cbn; lia|exact SS16].
  - apply T8F; [apply Z8Fi; clear; cbn; lia|clear; lia|clear; cbn; lia|]. apply T68; [apply Z68i; [clear; cbn; lia|left; clear; cbn; lia]|clear; lia|clear; cbn; lia|exact SS56].
  - apply T8F; [apply Z8Fi; clear; cbn; lia|clear; lia|clear; cbn; lia|]. apply T68; [apply Z68i; [clear; cbn; lia|left; clear; cbn; lia]|clear; lia|clear; cbn; lia|exact SS48].
  - apply T8F; [apply Z8Fi; clear; cbn; lia|clear; lia|clear; cbn; lia|]. apply T68; [apply Z68i; [clear; cbn; lia|left; clear; cbn; lia]|clear; lia|clear; cbn; lia|exact SS616].
  - apply T8F; [apply Z8Fp; clear - Hnch; cbn; lia|clear - Hparr Hnch; lia|clear - Hparr' G2 Hnch; cbn; lia|]. apply T68; [apply Z68p; clear - Hnch; cbn; lia|clear - Hparr Hnch; lia|clear - Hparr' G2 Hnch; cbn; lia|exact Sslot].
  - eapply wr_grows; [exact G6F|exact WSp].
Qed.
End Spec.
