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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatSecAlloc_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtSizeLog. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatPoisonRun_b BatPoison2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b
     BatCellEx_b BatImgCell_b BatSecAllocPost_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatUnwind_b BatCellJoin_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r719b0_719e8_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_sec_events (msz r parr nch : Z) (committed : bool) : list aev :=
  AMmapNull msz r :: (if committed then [] else [AMmapFixed (parr + 8 * nch) 131072]).

(* [comment removed for export] *)
Definition art_sec_fp (s t parr nch r msz : Z) (committed : bool) : list (Z * Z) :=
  [ (s - 464, 464); (0x13c618, 624); (0x13c888 + 16, 16); (t + 2872, 16); (r, msz); (art_shlo r, art_shhi r msz - art_shlo r);
    (parr + 8 * nch, if committed then 8 else 131072) ].

(* [comment removed for export] *)
Definition art_sec_grant (HI t ctx parr msz r : Z) : Prop :=
  r mod 4096 = 0 /\ 4096 <= r /\ 0x696000 <= r /\ r + msz <= HI /\ appmem r msz
  /\ apart r msz t 4096 /\ apart r msz ctx 4096 /\ apart r msz parr (2 ^ 23).

Lemma art_at_ecall_mmap2 : art_at_ecall ASEGS (0x8bc80 : word).
Proof. exists W_8b868. split; [exact F_8b868 | exact E_8b868]. Qed.

(* [comment removed for export] *)
Lemma art_sh_bounds : forall r msz, r mod 4096 = 0 -> msz mod 4096 = 0 -> 0 <= r -> 0 <= msz -> r + msz <= 2 ^ 47 ->
  SB <= art_shlo r /\ art_shlo r <= SB + r / 8 /\ SB + r / 8 + msz / 8 <= art_shhi r msz /\ art_shhi r msz <= kHighMemBeg
  /\ (r + msz) / 8 = r / 8 + msz / 8 /\ 8 * (r / 8) = r /\ 8 * (msz / 8) = msz.
Proof.
  intros r msz Hr Hm Hr0 Hm0 H47. unfold art_shlo, art_shhi, SB, kHighMemBeg.
  assert (Er : r = 4096 * (r / 4096)) by (pose proof (Z.div_mod r 4096 ltac:(lia)); lia).
  assert (Em : msz = 4096 * (msz / 4096)) by (pose proof (Z.div_mod msz 4096 ltac:(lia)); lia).
  set (kr := r / 4096) in *. set (km := msz / 4096) in *.
  assert (D1 : r / 8 = 512 * kr). { rewrite Er. replace (4096 * kr) with (512 * kr * 8) by lia. apply Z.div_mul. lia. }
  assert (D2 : msz / 8 = 512 * km). { rewrite Em. replace (4096 * km) with (512 * km * 8) by lia. apply Z.div_mul. lia. }
  assert (D3 : (r + msz) / 8 = 512 * kr + 512 * km). { rewrite Er, Em. replace (4096 * kr + 4096 * km) with ((512 * kr + 512 * km) * 8) by lia. apply Z.div_mul. lia. }
  rewrite D1, D2, D3.
  pose proof (Z.div_mod (512 * kr + 2147450880) 4096 ltac:(lia)) as Q1. pose proof (Z.mod_pos_bound (512 * kr + 2147450880) 4096 ltac:(lia)) as Q2.
  pose proof (Z.div_mod (512 * kr + 512 * km + 2147450880 + 4095) 4096 ltac:(lia)) as Q3. pose proof (Z.mod_pos_bound (512 * kr + 512 * km + 2147450880 + 4095) 4096 ltac:(lia)) as Q4.
  set (X := (512 * kr + 2147450880) / 4096) in *. set (Y := (512 * kr + 512 * km + 2147450880 + 4095) / 4096) in *.
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma art_lock_word_release : forall (M : word -> option byte) a, 0 <= a -> a + 4 < 2 ^ 64 -> cellA M a 4 1 -> cellA (Wn 1 M a 0) a 4 0.
Proof.
  intros M a Ha Ha' C.
  assert (C3 : cellA M (a + 1) 3 0).
  { unfold cell in *. pose proof (rdn_skipn _ _ _ _ _ 1%nat C ltac:(lia)) as S. cbn [Nat.sub] in S.
    replace (Z_to_bv 64 (a + 1) : word) with (Z_to_bv 64 a + nat_to_word 1)%bv.
    2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (Z.mod_small (Z.of_nat 1)) by (cbn; lia). rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (a + 1)) by lia. rewrite Z.mod_small by (cbn; lia). reflexivity. }
    rewrite S. reflexivity. }
  replace 0 with (0 + 0 * 2 ^ (8 * Z.of_nat 1)) at 2 by lia.
  apply (art_cell_join (Wn 1 M a 0) a 1 3 0 0); [lia|cbn; lia|lia|cbn; lia|cbn; lia|apply cell_Wn_hit; [lia|cbn; lia]|].
  apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact C3.
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Ltac sec_side :=
  first [ assumption
        | lia
        | lazymatch goal with
          | |- _ mod _ = _ => reflexivity
          | |- getr _ _ = _ => gres; first [reflexivity | assumption]
          | |- _ /\ _ => split; sec_side
          end ].
Ltac sec_feed H :=
  repeat lazymatch type of H with
    | ?P -> _ => let HP := fresh "HP" in assert (HP : P) by sec_side; specialize (H HP); clear HP
    end.

#[using="Type"] Theorem art_sec_rspec_holds :
  forall (Q : list aev -> machine_state -> Prop) (P : Z -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
         (s HI n q msz nm tp key tsd ctx t parr nch : Z) (committed : bool),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = Z_to_bv 64 0x13c618 -> getr regs 11 = Z_to_bv 64 0x13c888 -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
    65536 < n < 2 ^ 40 -> n mod 8 = 0 -> 4096 * (q - 1) < n <= 4096 * q -> msz = 4096 * q + 4096 ->
    (* [comment removed for export] *)
    kHighMemBeg <= HI -> HI <= s - 464 -> s < 2 ^ 47 ->
    ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x696000 <= t) -> t + 4096 <= HI -> appmem t 4096 ->
    4096 <= ctx -> ctx + 4096 <= HI -> appmem ctx 4096 -> apart t 4096 ctx 4096 ->
    4096 <= tp - 88 -> tp < 0x696000 -> 4096 <= tsd -> tsd + 8 * key + 8 <= 0x696000 ->
    0x696000 <= parr -> parr mod 4096 = 0 -> parr + 2 ^ 23 <= HI -> appmem parr (2 ^ 23) -> apart parr (2 ^ 23) t 4096 ->
    0 <= nch < 16384 -> (committed = false -> nch = 0) -> 0x10000 <= nm < 2 ^ 47 ->
    (* [comment removed for export] *)
    wrA M (s - 464) 464 -> wrA M t 4096 -> (committed = true -> wrA M parr 131072) ->
    cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M (0x1d1768 + 260) 1 0 -> cellA M (0x1d1768 + 144) 8 0 ->
    cellA M 0x1374a8 8 0x139508 -> cellA M 0x139508 8 nm ->
    art_layout M -> art_tsd M tp key tsd ctx t ->
    cellA M 0x13c618 8 4096 -> cellA M (0x13c618 + 8) 8 parr -> cellA M (0x13c618 + 16) 8 parr -> cellA M (0x13c618 + 56) 8 nch ->
    cellA M (0x13c618 + 48) 8 (if committed then 16384 else 0) -> cellA M (0x13c618 + 616) 4 0 ->
    (* [comment removed for export] *)
    (forall Mx r, GR log Mx msz r -> P r) -> (forall r, P r -> art_sec_grant HI t ctx parr msz r) ->
    EVOK log (AMmapNull msz 0) ->
    (committed = false -> forall r, P r -> EVOK (log ++ [AMmapNull msz r]) (AMmapFixed (parr + 8 * nch) 131072)) ->
    (* [comment removed for export] *)
    (forall r regs' (M' : word -> option byte), P r ->
       getr regs' 10 = Z_to_bv 64 (4096 + r) -> getr regs' 2 = Z_to_bv 64 s -> getr regs' 1 = raw ->
       (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x) ->
       mem_grows M M' -> art_agree (art_sec_fp s t parr nch r msz committed) M M' ->
       (forall (x : word) b, art_shlo r <= U x < art_shhi r msz -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> M x = Some b -> M' x = Some b) ->
       wrA M' r msz -> wrA M' (SB + r / 8) (msz / 8) ->
       cellA M' r 8 r -> cellA M' (r + 8) 8 msz -> cellA M' (r + 16) 8 n -> cellA M' (r + 24) 8 nch ->
       (forall x : word, r + 32 <= U x < r + msz -> M' x = Some (Z_to_bv 8 0)) ->
       cellA M' 0x13c618 8 4096 -> cellA M' (0x13c618 + 8) 8 parr -> cellA M' (0x13c618 + 16) 8 parr -> cellA M' (0x13c618 + 56) 8 (nch + 1) ->
       cellA M' (0x13c618 + 48) 8 16384 -> cellA M' (0x13c618 + 616) 4 0 ->
       cellA M' (parr + 8 * nch) 8 r -> wrA M' parr 131072 ->
       Q (log ++ art_sec_events msz r parr nch committed) (mkst regs' raw M' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst regs (0x57014 : word) M rom).
Proof.
  intros Q P log regs M rom raw s HI n q msz nm tp key tsd ctx t parr nch committed.
  intros H1 Hret H2 H4 H10 H11 H12 H13 Hn Hn8 Hq Emsz.
  intros HHI Hs Hs' Ht Ht' APt Hctx Hctx' APc Atc Htp Htp' Htsd Htsd' Hparr Hparr4 Hparr' APp Apt Hnch Hnch0 Hnm.
  intros W Wt Wparr Cg28 Cpc Cfb C144 Cnm1 Cnm2 LAY TSD Cpg Cpab Cpab2 Cnch Cnres Clk HGR HP EV1 EV2 HK.
  unfold kHighMemBeg in HHI.
  assert (Ht0 : 4096 <= t) by (clear - Ht; lia).
  change (hid ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x696000 <= t)) in Ht.
  pose proof LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CF & _).
  (* [comment removed for export] *)
  pose proof (art_sec_pre_fn regs M rom raw s 0x13c618 0x13c888 n q nm 0x1d1768 0 H1 H2 H10 H11 H12 H13 ltac:(lia) Hs' Hn ltac:(lia) Hq
                ltac:(lia) ltac:(lia) Hnm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
                ltac:(eapply wr_sub; [exact W|lia|lia]) Cpg Cnm1 Cnm2 Cg28 Cpc CF Cfb) as RUN1.
  rewrite <- Emsz in RUN1.
  lazymatch type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (R1 := R) in RUN1; set (M0 := MM) in RUN1 end.
  eapply ar_steps; [exact RUN1|]. clear RUN1.
  assert (ARGS : art_mmap_args R1 0 msz 34).
  { unfold art_mmap_args, R1. repeat split; gres; reflexivity. }
  eapply (ar_mmap_null ASEGS EVOK GR Q log R1 (0x8bc80 : word) (0x8bc84 : word) M0 rom msz art_at_ecall_mmap2 ltac:(apply bv_eq; reflexivity) ARGS EV1).
  intros r GRr. pose proof (HGR _ _ GRr) as Pr. clear GRr.
  destruct (HP r Pr) as (Hr4 & Hr & Hri & Hrm & APr & Art & Arc & Arp).
  assert (Hm4 : msz mod 4096 = 0). { rewrite Emsz. replace (4096 * q + 4096) with ((q + 1) * 4096) by lia. apply Z_mod_mult. }
  assert (Hq1 : 17 <= q) by lia.
  destruct (art_sh_bounds r msz Hr4 Hm4 ltac:(lia) ltac:(lia) ltac:(lia)) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7).
  unfold SB, kHighMemBeg in SH1, SH2, SH3, SH4.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  set (M1 := art_reveal (art_zfill M0 r msz) lo hi).
  set (R1r := regupd R1 10 (Z_to_bv 64 r)).
  (* [comment removed for export] *)
  assert (G01 : mem_grows M M1). { unfold M1, M0, art_sec_pre_mem. zgrows. }
  assert (A01 : art_agree [(s - 464, 464); (r, msz); (lo, hi - lo)] M M1).
  { unfold M1, M0, art_sec_pre_mem. eapply art_agree_sub; [zagree|]. clear - Hs Hs' HHI. zsub. }
  assert (AP1 : apart r msz (s - 464) 464) by (clear - Hrm Hs; unfold apart; lia).
  assert (AP2 : apart (t + 2872) 16 r 32) by (clear - Art Hq1 Emsz; unfold apart in *; lia).
  assert (AP3 : apart (t + 2872) 16 (s - 464) 464) by (clear - Ht' Hs; unfold apart; lia).
  assert (AP4 : apart (t + 2872) 16 (ctx + 152) 8) by (clear - Atc; unfold apart in *; lia).
  assert (AP5 : appmem (parr + 8 * nch) 8) by (clear - APp Hnch; unfold appmem in *; lia).
  assert (AP6 : apart (parr + 8 * nch) 8 r 32) by (clear - Arp Hnch Hq1 Emsz; unfold apart in *; lia).
  assert (AP7 : apart (parr + 8 * nch) 8 (s - 464) 464) by (clear - Hparr' Hs Hnch; unfold apart; lia).
  assert (AP8 : apart (parr + 8 * nch) 8 (t + 2872) 16) by (clear - Apt Hnch; unfold apart in *; lia).
  assert (AP9 : apart (ctx + 152) 8 r 32) by (clear - Arc Hq1 Emsz; unfold apart in *; lia).
  assert (AP10 : apart (ctx + 152) 8 (s - 464) 464) by (clear - Hctx' Hs; unfold apart; lia).
  assert (AP11 : apart r 32 (s - 464) 464) by (clear - Hrm Hs Hq1 Emsz; unfold apart; lia).
  (* [comment removed for export] *)
  assert (GAPt : art_gap [(s - 464, 464); (r, msz); (lo, hi - lo)] t 4096).
  { clear - APt Art Ht' Hs SH1 SH4. unfold appmem, SB, kHighMemBeg in APt. unfold apart in Art. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GAPc : art_gap [(s - 464, 464); (r, msz); (lo, hi - lo)] ctx 4096).
  { clear - APc Arc Hctx' Hs SH1 SH4. unfold appmem, SB, kHighMemBeg in APc. unfold apart in Arc. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GAPp : art_gap [(s - 464, 464); (r, msz); (lo, hi - lo)] parr (2 ^ 23)).
  { clear - APp Arp Hparr' Hs SH1 SH4. unfold appmem, SB, kHighMemBeg in APp. unfold apart in Arp. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GAPi : art_gap [(s - 464, 464); (r, msz); (lo, hi - lo)] 0x10000 (0x696000 - 0x10000)).
  { clear - Hri HHI Hs SH1. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (AGimg : forall x : word, U x < 0x696000 -> M1 x = M x).
  { intros x Hx. apply (art_agree_pt _ _ _ x A01). pose proof (bv_unsigned_in_range 64 x). clear - Hx Hri HHI Hs SH1 H. cbn [art_out fst snd]. repeat split; try exact I; lia. }
  assert (AGctx : forall x : word, ctx + 152 <= U x < ctx + 160 -> M1 x = M x).
  { intros x Hx. apply (art_agree_pt _ _ _ x A01). eapply art_gap_out; [exact GAPc|lia]. }
  assert (LAY1 : art_layout M1) by (apply (art_layout_agree M M1 AGimg LAY)).
  assert (TSD1 : art_tsd M1 tp key tsd ctx t) by (apply (art_tsd_agree M M1 tp key tsd ctx t AGimg AGctx Htp' Htsd' TSD)).
  assert (W1a : wrA M1 (s - 464) 464). { unfold M1. apply wr_reveal_other, wr_zfill_other. unfold M0, art_sec_pre_mem. repeat apply wr_Wn. exact W. }
  assert (W1r : wrA M1 r msz). { unfold M1. apply wr_reveal_other. apply wr_zfill; lia. }
  assert (W1b : wrA M1 r 32) by (eapply wr_sub; [exact W1r|lia|lia]).
  assert (W1s : wrA M1 (SB + r / 8) (msz / 8)). { unfold M1. eapply wr_sub; [apply wr_reveal; lia| unfold SB; lia | unfold SB; lia]. }
  assert (W1t : wrA M1 (t + 2872) 16). { eapply wr_grows; [exact G01|]. eapply wr_sub; [exact Wt|lia|lia]. }
  assert (W1sec : wrA M1 0x13c618 624) by (apply art_img_wr; lia).
  assert (W1st : wrA M1 (0x13c888 + 16) 16) by (apply art_img_wr; lia).
  (* [comment removed for export] *)
  assert (FC : forall a (k : nat) v, s - 464 <= a -> a + Z.of_nat k <= s -> cellA M0 a k v -> cellA M1 a k v).
  { intros a k v Ha Hk C. unfold M1. apply cell_reveal_other; [lia|lia|clear - Ha Hk SH4 HHI Hs; unfold apart; lia|].
    apply cell_zfill_other; [lia|lia|clear - Ha Hk Hrm Hs; unfold apart; lia|exact C]. }
  assert (F104 : cellA M1 (s - 104) 8 0x570d0) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F112 : cellA M1 (s - 112) 8 0x13c888) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F120 : cellA M1 (s - 120) 8 0x13c618) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F128 : cellA M1 (s - 128) 8 msz) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F8 : cellA M1 (s - 8) 8 (U raw)) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F16 : cellA M1 (s - 16) 8 (U (getr regs 8))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F24 : cellA M1 (s - 24) 8 (U (getr regs 9))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F32 : cellA M1 (s - 32) 8 (U (getr regs 18))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F40 : cellA M1 (s - 40) 8 (U (getr regs 19))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F48 : cellA M1 (s - 48) 8 (U (getr regs 20))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F56 : cellA M1 (s - 56) 8 (U (getr regs 21))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F64 : cellA M1 (s - 64) 8 (U (getr regs 22))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F72 : cellA M1 (s - 72) 8 (U (getr regs 23))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F80 : cellA M1 (s - 80) 8 (U (getr regs 24))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  assert (F88 : cellA M1 (s - 88) 8 (U (getr regs 25))) by (apply FC; [lia|cbn; lia|unfold M0, art_sec_pre_mem; clear - Hs Hs' HHI; zcell]).
  (* [comment removed for export] *)
  assert (IC : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x696000 -> cellA M a k v -> cellA M1 a k v).
  { intros a k v Ha Hk C. apply (art_cell_tr _ M M1 a k v A01); [eapply art_gap_sub; [exact GAPi|lia|lia]|lia|lia|exact C]. }
  assert (I1 : cellA M1 0x13c618 8 4096) by (apply IC; [lia|cbn; lia|exact Cpg]).
  assert (I2 : cellA M1 0x1374b0 8 0x1d1768) by (apply IC; [lia|cbn; lia|exact CF]).
  assert (I3 : cellA M1 (0x1d1768 + 144) 8 0) by (apply IC; [lia|cbn; lia|exact C144]).
  assert (I4 : cellA M1 (0x13c618 + 616) 4 0) by (apply IC; [lia|cbn; lia|exact Clk]).
  assert (I5 : cellA M1 (0x13c618 + 56) 8 nch) by (apply IC; [lia|cbn; lia|exact Cnch]).
  assert (I6 : cellA M1 (0x13c618 + 48) 8 (if committed then 16384 else 0)) by (apply IC; [lia|cbn; lia|exact Cnres]).
  assert (I7 : cellA M1 (0x13c618 + 8) 8 parr) by (apply IC; [lia|cbn; lia|exact Cpab]).
  assert (I8 : cellA M1 (0x13c618 + 16) 8 parr) by (apply IC; [lia|cbn; lia|exact Cpab2]).
  assert (I9 : cellA M1 0x1374a0 8 0x1cf6e0) by (apply IC; [lia|cbn; lia|exact Cg28]).
  assert (I10 : cellA M1 0x1cf6e0 8 4096) by (apply IC; [lia|cbn; lia|exact Cpc]).
  (* [comment removed for export] *)
  assert (Toff : t + 2872 + 16 <= 0x10000 \/ 0x696000 <= t + 2872) by (clear - Ht; unfold hid in Ht; lia).
  destruct (art_cell_exists M1 (t + 2872) 8 ltac:(lia) ltac:(cbn; clear - Toff; lia) ltac:(clear - Ht; unfold hid in Ht; lia) ltac:(cbn; clear - Ht' Hs Hs'; lia) ltac:(eapply wr_sub; [exact W1t|lia|cbn; lia])) as (C & HC & CC).
  destruct (art_cell_exists M1 (t + 2880) 8 ltac:(lia) ltac:(cbn; clear - Toff; lia) ltac:(clear - Ht; unfold hid in Ht; lia) ltac:(cbn; clear - Ht' Hs Hs'; lia) ltac:(eapply wr_sub; [exact W1t|lia|cbn; lia])) as (D & HD & CD).
  clear Toff.
  assert (HL : 12 <= Z.log2 msz <= 46).
  { split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  destruct (art_img_cell_exists M1 (0x13c618 + 72) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (na & Hna & Cna). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hna.
  destruct (art_img_cell_exists M1 (0x13c618 + 88) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (cur & Hcur & Ccur). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hcur.
  destruct (art_img_cell_exists M1 (0x13c618 + 96) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (mx & Hmx & Cmx). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hmx.
  destruct (art_img_cell_exists M1 (0x13c618 + 104 + 8 * Z.log2 msz) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bsl & Hbsl & Cbsl). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hbsl.
  destruct (art_img_cell_exists M1 (0x13c888 + 16) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (st16 & H16 & C16). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H16.
  destruct (art_img_cell_exists M1 (0x13c888 + 24) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (st24 & H24 & C24). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H24.
  assert (X1 : getr R1r 1 = Z_to_bv 64 0x8d5d0) by (unfold R1r, R1; gres; reflexivity).
  assert (X2 : getr R1r 2 = Z_to_bv 64 (s - 144)) by (unfold R1r, R1; gres; reflexivity).
  assert (X4 : getr R1r 4 = Z_to_bv 64 tp) by (unfold R1r, R1; gres; exact H4).
  assert (X10 : getr R1r 10 = Z_to_bv 64 r) by (unfold R1r, R1; gres; reflexivity).
  assert (X19 : getr R1r 19 = Z_to_bv 64 n) by (unfold R1r, R1; gres; reflexivity).
  assert (X21 : getr R1r 21 = Z_to_bv 64 8) by (unfold R1r, R1; gres; reflexivity).
  assert (X24 : getr R1r 24 = Z_to_bv 64 7) by (unfold R1r, R1; gres; reflexivity).
  assert (XK : forall x : reg, In x [3; 4; 26; 27]%bv -> getr R1r x = getr regs x).
  { intros x Hx. cbn [In] in Hx. unfold R1r, R1. destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity. }
  assert (Hkh : 0x10007fff8000 <= s - 464) by lia.
  fold (regupd R1 10 (Z_to_bv 64 r)). fold R1r. fold M1.
  destruct committed.
  - (* [comment removed for export] *)
    assert (W1p : wrA M1 (parr + 8 * nch) 8). { eapply wr_grows; [exact G01|]. eapply wr_sub; [exact (Wparr eq_refl)|lia|lia]. }
    pose proof (art_sec_postA_run R1r M1 rom raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                  (getr regs 23) (getr regs 24) (getr regs 25) s 0x13c618 0x13c888 msz n r 0x1d1768 tp key tsd ctx t C D nch 16384 parr na cur mx bsl st16 st24) as POST.
    unfold kHighMemBeg in POST.
    sec_feed POST.
    lazymatch type of POST with ?P -> _ => fail "UNFED:" P | _ => idtac end.
    destruct POST as (regs' & RUN & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E4 & E3 & E26 & E27).
    lazymatch type of RUN with msteps _ _ (mkst _ _ ?MM _) => set (MF := MM) in RUN end.
    eapply ar_steps; [exact RUN|]. clear RUN. apply ar_done.
    assert (TL0 : 0 <= (msz - 4096 - n) / 8) by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (msz - 4096 - n) 8 ltac:(lia)) as TL1.
    pose proof (Z.mul_div_le (4096 + r + n) 8 ltac:(lia)) as TA1. pose proof (Z.mul_succ_div_gt (4096 + r + n) 8 ltac:(lia)) as TA2.
    assert (K512 : 4096 / 8 = 512) by reflexivity.
    assert (G1F : mem_grows M1 MF). { unfold MF, sec_postA_mem, sec_tail_mem, sec_hm, sec_pm2, sec_pm1, art_poison_frame. zgrows. }
    assert (A1F : art_agree [(s - 464, 464); (0x13c618, 624); (0x13c888 + 16, 16); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (parr + 8 * nch, 8)] M1 MF).
    { unfold MF, sec_postA_mem, sec_tail_mem, sec_hm, sec_pm2, sec_pm1, art_poison_frame, SB. eapply art_agree_sub; [zagree|].
      rewrite K512. intros z. clear - Hs Hs' HHI HL TL0 TL1 TA1 TA2 SH6 SH7 Hr Hn Hq1 Emsz. intros Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
    assert (AH : art_agree [(s - 464, 464); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (0x13c618 + 616, 4)] M1 (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D)).
    { unfold sec_hm, sec_pm2, sec_pm1, art_poison_frame, SB. eapply art_agree_sub; [zagree|].
      rewrite K512. intros z. clear - Hs Hs' HHI TL0 TL1 TA1 TA2 SH6 SH7 Hr Hn Hq1 Emsz. intros Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
    assert (HCI : forall a (k : nat) v, 0x13c618 <= a -> a + Z.of_nat k <= 0x13c618 + 616 -> cellA M1 a k v -> cellA (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D) a k v).
    { intros a k v Ha Hk Cc. apply (art_cell_tr _ _ _ a k v AH); [|lia|lia|exact Cc].
      clear - Ha Hk Hkh Hri Ht SH1. unfold hid in Ht. unfold SB. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
    assert (HC0 : cellA (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D) 0x13c618 8 4096) by (apply HCI; [lia|cbn; lia|exact I1]).
    assert (HC8 : cellA (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D) (0x13c618 + 8) 8 parr) by (apply HCI; [lia|cbn; lia|exact I7]).
    assert (HC16 : cellA (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D) (0x13c618 + 16) 8 parr) by (apply HCI; [lia|cbn; lia|exact I8]).
    assert (HC48 : cellA (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D) (0x13c618 + 48) 8 16384) by (apply HCI; [lia|cbn; lia|exact I6]).
    apply (HK r regs' MF Pr).
    + exact E10.
    + exact E2.
    + exact E1.
    + intros x Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        first [ exact E8 | exact E9 | exact E18 | exact E19 | exact E20 | exact E21 | exact E22 | exact E23 | exact E24 | exact E25
              | (rewrite E3; apply XK; inl) | (rewrite E4; symmetry; exact H4) | (rewrite E26; apply XK; inl) | (rewrite E27; apply XK; inl) ].
    + eapply mem_grows_trans; [exact G01|exact G1F].
    + eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A01 A1F)|].
      unfold art_sec_fp, SB. intros z. clear - SH2 SH3 Hq1 Emsz. fold lo hi. intros Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia.
    + intros x b Hx Nx Mx. pose proof (bv_unsigned_in_range 64 x) as Rx.
      rewrite (art_agree_pt _ _ _ x A1F).
      2:{ clear - Hx Nx SH1 SH4 Hkh APt APp APr Hq1 Emsz Hnch Hri. unfold appmem, SB, kHighMemBeg in *. cbn [art_out fst snd]. repeat split; try exact I; lia. }
      unfold M1. apply art_reveal_some. rewrite art_zfill_out by (clear - Hx SH1 SH4 APr; unfold appmem, SB, kHighMemBeg in *; lia).
      rewrite (art_agree_pt [(s - 464, 464)] M M0 x); [exact Mx| |].
      * unfold M0, art_sec_pre_mem. eapply art_agree_sub; [zagree|]. clear - Hs Hs' HHI. zsub.
      * clear - Hx SH4 Hkh. cbn [art_out fst snd]. repeat split; try exact I; lia.
    + eapply wr_grows; [exact G1F|exact W1r].
    + eapply wr_grows; [exact G1F|exact W1s].
    + unfold MF, sec_postA_mem, sec_tail_mem, sec_hm. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem, sec_hm. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem, sec_hm. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem, sec_hm. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx.
      rewrite (art_agree_pt _ _ _ x A1F).
      2:{ clear - Hx AP1 Hri Art Arp Hnch APr SH6 SH7 Hq1 Emsz Hrm Hs Hs'. unfold appmem, SB, kHighMemBeg, apart in *. cbn [art_out fst snd]. repeat split; try exact I; lia. }
      unfold M1. apply art_reveal_some. apply art_zfill_in. lia.
    + unfold MF, sec_postA_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem. apply art_lock_word_release; [lia|lia|]. unfold sec_hm. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + unfold MF, sec_postA_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HC0 HC8 HC16 HC48 I1 I4 I5 I6 I7 I8; zcell.
    + eapply wr_grows; [eapply mem_grows_trans; [exact G01|exact G1F]|exact (Wparr eq_refl)].
  - (* [comment removed for export] *)
    pose proof (Hnch0 eq_refl) as N0. subst nch. clear Hnch0.
    assert (PM : (parr + 8 * 0) mod 4096 = 0) by (replace (parr + 8 * 0) with parr by lia; exact Hparr4).
    pose proof (art_sec_postB1_run R1r M1 rom s 0x13c618 0x13c888 msz n r 0x1d1768 tp key tsd ctx t C D 0 parr) as POST1.
    unfold kHighMemBeg in POST1.
    sec_feed POST1.
    lazymatch type of POST1 with ?P -> _ => fail "UNFED:" P | _ => idtac end.
    destruct POST1 as (rb & RUNB & B17 & B10 & B11 & B12 & B13 & B14 & B15 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B4 & B3 & B26 & B27).
    lazymatch type of RUNB with msteps _ _ (mkst _ _ ?MM _) => set (MB1 := MM) in RUNB end.
    eapply ar_steps; [exact RUNB|]. clear RUNB.
    assert (ARGS2 : art_mmap_args rb (parr + 8 * 0) 131072 50).
    { unfold art_mmap_args. repeat split; assumption. }
    eapply (ar_mmap_fixed ASEGS EVOK GR Q (log ++ [AMmapNull msz r]) rb (0x8bc80 : word) (0x8bc84 : word) MB1 rom (parr + 8 * 0) 131072
              art_at_ecall_mmap2 ltac:(apply bv_eq; reflexivity) ARGS2 (EV2 eq_refl r Pr)).
    set (M2 := art_zfill MB1 (parr + 8 * 0) 131072). set (R2 := regupd rb 10 (Z_to_bv 64 (parr + 8 * 0))).
    assert (TL0 : 0 <= (msz - 4096 - n) / 8) by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (msz - 4096 - n) 8 ltac:(lia)) as TL1.
    pose proof (Z.mul_div_le (4096 + r + n) 8 ltac:(lia)) as TA1. pose proof (Z.mul_succ_div_gt (4096 + r + n) 8 ltac:(lia)) as TA2.
    assert (K512 : 4096 / 8 = 512) by reflexivity.
    assert (G12 : mem_grows M1 M2). { unfold M2, MB1, sec_b1_mem, sec_hm, sec_pm2, sec_pm1, art_poison_frame. zgrows. }
    assert (A12 : art_agree [(s - 464, 368); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (0x13c618 + 616, 4); (parr + 8 * 0, 131072)] M1 M2).
    { unfold M2, MB1, sec_b1_mem, sec_hm, sec_pm2, sec_pm1, art_poison_frame, SB. eapply art_agree_sub; [zagree|].
      rewrite K512. intros z. clear - Hs Hs' HHI HL TL0 TL1 TA1 TA2 SH6 SH7 Hr Hn Hq1 Emsz. intros Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
    (* [comment removed for export] *)
    assert (TC : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                   art_gap [(s - 464, 368); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (0x13c618 + 616, 4); (parr + 8 * 0, 131072)] a (Z.of_nat k) ->
                   cellA M1 a k v -> cellA M2 a k v).
    { intros a k v Ha Hk Gp Cc. exact (art_cell_tr _ _ _ a k v A12 Gp Ha Hk Cc). }
    assert (GI : forall a n0, 0x10000 <= a -> 0 <= n0 -> a + n0 <= 0x13c618 + 616 ->
                   art_gap [(s - 464, 368); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (0x13c618 + 616, 4); (parr + 8 * 0, 131072)] a n0).
    { intros a n0 Ha Hn0 Hn1. clear - Ha Hn0 Hn1 Hkh Hri Ht SH1 Hparr. unfold hid in Ht. unfold SB. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
    assert (GS : forall a n0, s - 96 <= a -> 0 <= n0 -> a + n0 <= s ->
                   art_gap [(s - 464, 368); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (0x13c618 + 616, 4); (parr + 8 * 0, 131072)] a n0).
    { intros a n0 Ha Hn0 Hn1. clear - Ha Hn0 Hn1 Hkh Hs Hs' Hparr' AP3 AP11 AP7 SH3 SH4 SH6 SH7. unfold SB, kHighMemBeg, apart in *. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
    assert (J1 : cellA M2 0x1374b0 8 0x1d1768) by (apply TC; [lia|cbn; lia|apply GI; cbn; lia|exact I2]).
    assert (J2 : cellA M2 (0x1d1768 + 144) 8 0). { apply TC; [lia|cbn; lia| |exact I3]. clear - Hkh Hri Ht SH1 Hparr. unfold hid in Ht. unfold SB. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; cbn; lia. }
    assert (J3 : cellA M2 (0x13c618 + 48) 8 0) by (apply TC; [lia|cbn; lia|apply GI; cbn; lia|exact I6]).
    assert (J4 : cellA M2 (0x13c618 + 56) 8 0) by (apply TC; [lia|cbn; lia|apply GI; cbn; lia|exact I5]).
    assert (J5 : cellA M2 (0x13c618 + 8) 8 parr) by (apply TC; [lia|cbn; lia|apply GI; cbn; lia|exact I7]).
    assert (JF8 : cellA M2 (s - 8) 8 (U raw)) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F8]).
    assert (JF16 : cellA M2 (s - 16) 8 (U (getr regs 8))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F16]).
    assert (JF24 : cellA M2 (s - 24) 8 (U (getr regs 9))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F24]).
    assert (JF32 : cellA M2 (s - 32) 8 (U (getr regs 18))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F32]).
    assert (JF40 : cellA M2 (s - 40) 8 (U (getr regs 19))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F40]).
    assert (JF48 : cellA M2 (s - 48) 8 (U (getr regs 20))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F48]).
    assert (JF56 : cellA M2 (s - 56) 8 (U (getr regs 21))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F56]).
    assert (JF64 : cellA M2 (s - 64) 8 (U (getr regs 22))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F64]).
    assert (JF72 : cellA M2 (s - 72) 8 (U (getr regs 23))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F72]).
    assert (JF80 : cellA M2 (s - 80) 8 (U (getr regs 24))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F80]).
    assert (JF88 : cellA M2 (s - 88) 8 (U (getr regs 25))) by (apply TC; [lia|cbn; lia|apply GS; cbn; lia|exact F88]).
    (* [comment removed for export] *)
    assert (ZC : forall a (k : nat) v, s - 464 <= a -> a + Z.of_nat k <= s -> cellA MB1 a k v -> cellA M2 a k v).
    { intros a k v Ha Hk Cc. unfold M2. apply cell_zfill_other; [lia|lia|clear - Ha Hk Hparr' Hs; unfold apart; lia|exact Cc]. }
    assert (JB104 : cellA M2 (s - 104) 8 0x57470) by (apply ZC; [lia|cbn; lia|unfold MB1, sec_b1_mem; clear - Hs Hs' HHI Hkh HL Hr Hrm; zcell]).
    assert (JB112 : cellA M2 (s - 112) 8 0x13c888) by (apply ZC; [lia|cbn; lia|unfold MB1, sec_b1_mem; clear - Hs Hs' HHI Hkh HL Hr Hrm; zcell]).
    assert (JB120 : cellA M2 (s - 120) 8 0x13c618) by (apply ZC; [lia|cbn; lia|unfold MB1, sec_b1_mem; clear - Hs Hs' HHI Hkh HL Hr Hrm; zcell]).
    assert (JB128 : cellA M2 (s - 128) 8 msz) by (apply ZC; [lia|cbn; lia|unfold MB1, sec_b1_mem; clear - Hs Hs' HHI Hkh HL Hr Hrm; zcell]).
    assert (JB136 : cellA M2 (s - 136) 8 (63 - Z.log2 msz)) by (apply ZC; [lia|cbn; lia|unfold MB1, sec_b1_mem; clear - Hs Hs' HHI Hkh HL Hr Hrm; zcell]).
    assert (JB144 : cellA M2 (s - 144) 8 (4096 + r)) by (apply ZC; [lia|cbn; lia|unfold MB1, sec_b1_mem; clear - Hs Hs' HHI Hkh HL Hr Hrm; zcell]).
    assert (W2a : wrA M2 (s - 464) 464) by (eapply wr_grows; [exact G12|exact W1a]).
    assert (W2sec : wrA M2 0x13c618 624) by (apply art_img_wr; lia).
    assert (W2st : wrA M2 (0x13c888 + 16) 16) by (apply art_img_wr; lia).
    assert (W2r : wrA M2 (r + 24) 8) by (eapply wr_grows; [exact G12|]; eapply wr_sub; [exact W1r|lia|lia]).
    assert (W2p : wrA M2 (parr + 8 * 0) 8). { unfold M2. eapply wr_sub; [apply wr_zfill; lia|lia|lia]. }
    destruct (art_img_cell_exists M2 (0x13c618 + 72) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (na2 & Hna2 & Cna2). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hna2.
    destruct (art_img_cell_exists M2 (0x13c618 + 88) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (cur2 & Hcur2 & Ccur2). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hcur2.
    destruct (art_img_cell_exists M2 (0x13c618 + 96) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (mx2 & Hmx2 & Cmx2). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hmx2.
    destruct (art_img_cell_exists M2 (0x13c618 + 104 + 8 * Z.log2 msz) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bsl2 & Hbsl2 & Cbsl2). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hbsl2.
    destruct (art_img_cell_exists M2 (0x13c888 + 16) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (s16 & Hs16 & Cs16). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hs16.
    destruct (art_img_cell_exists M2 (0x13c888 + 24) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (s24 & Hs24 & Cs24). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hs24.
    assert (Y1 : getr R2 1 = Z_to_bv 64 0x8da40) by (unfold R2; gres; exact B1).
    assert (Y2 : getr R2 2 = Z_to_bv 64 (s - 192)) by (unfold R2; gres; exact B2).
    assert (Y4 : getr R2 4 = Z_to_bv 64 tp) by (unfold R2; gres; exact B4).
    assert (Y8 : getr R2 8 = Z_to_bv 64 131072) by (unfold R2; gres; exact B8).
    assert (Y10 : getr R2 10 = Z_to_bv 64 (parr + 8 * 0)) by (unfold R2; gres; reflexivity).
    assert (Y21 : getr R2 21 = Z_to_bv 64 r) by (unfold R2; gres; exact B21).
    pose proof (art_sec_postB2_run R2 M2 rom raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                  (getr regs 23) (getr regs 24) (getr regs 25) s 0x13c618 0x13c888 msz r 0x1d1768 tp 0 0 (parr + 8 * 0) parr na2 cur2 mx2 bsl2 s16 s24) as POST2.
    sec_feed POST2.
    lazymatch type of POST2 with ?P -> _ => fail "UNFED:" P | _ => idtac end.
    destruct POST2 as (regs' & RUN & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E4 & E3 & E26 & E27).
    lazymatch type of RUN with msteps _ _ (mkst _ _ ?MM _) => set (MF := MM) in RUN end.
    eapply ar_steps; [exact RUN|]. clear RUN. apply ar_done.
    assert (G2F : mem_grows M2 MF). { unfold MF, sec_postB_mem, sec_tail_mem. zgrows. }
    assert (A2F : art_agree [(s - 464, 368); (0x13c618, 624); (0x13c888 + 16, 16); (r, 32); (parr + 8 * 0, 8)] M2 MF).
    { unfold MF, sec_postB_mem, sec_tail_mem. eapply art_agree_sub; [zagree|].
      intros z. clear - Hs Hs' HHI HL Hr. intros Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
    assert (A1F : art_agree [(s - 464, 464); (0x13c618, 624); (0x13c888 + 16, 16); (t + 2872, 16); (r, 32); (SB + r / 8, msz / 8); (parr + 8 * 0, 131072)] M1 MF).
    { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A12 A2F)|].
      intros z. clear. intros Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
    assert (AHB : art_agree [(s - 464, 368); (parr + 8 * 0, 131072)] (sec_hm M1 s 0x13c888 0x13c618 msz n r t C D) M2).
    { unfold M2, MB1, sec_b1_mem. eapply art_agree_sub; [zagree|]. intros z. clear - Hs Hs' HHI. intros Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
    assert (GHB : forall a n0, 0 <= n0 -> (0x10000 <= a /\ a + n0 <= 0x696000) \/ (r <= a /\ a + n0 <= r + 32) -> art_gap [(s - 464, 368); (parr + 8 * 0, 131072)] a n0).
    { intros a n0 Hn0 Ha. clear - Hn0 Ha Hkh Hparr AP1 Arp Hq1 Emsz. unfold apart in *. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
    assert (HBr : cellA M2 r 8 r) by (apply (art_cell_tr _ _ _ r 8 r AHB); [apply GHB; cbn; lia|lia|cbn; lia|unfold sec_hm; clear - Hs Hs' HHI Hkh Hr Hri Hrm Ht0 Ht' AP2 AP11 Hq1 Emsz Hn; zcell]).
    assert (HBr8 : cellA M2 (r + 8) 8 msz) by (apply (art_cell_tr _ _ _ (r + 8) 8 msz AHB); [apply GHB; cbn; lia|lia|cbn; lia|unfold sec_hm; clear - Hs Hs' HHI Hkh Hr Hri Hrm Ht0 Ht' AP2 AP11 Hq1 Emsz Hn; zcell]).
    assert (HBr16 : cellA M2 (r + 16) 8 n) by (apply (art_cell_tr _ _ _ (r + 16) 8 n AHB); [apply GHB; cbn; lia|lia|cbn; lia|unfold sec_hm; clear - Hs Hs' HHI Hkh Hr Hri Hrm Ht0 Ht' AP2 AP11 Hq1 Emsz Hn; zcell]).
    assert (HBlk : cellA M2 (0x13c618 + 616) 4 1) by (apply (art_cell_tr _ _ _ (0x13c618 + 616) 4 1 AHB); [apply GHB; cbn; lia|lia|cbn; lia|unfold sec_hm; apply cell_Wn_hit; [lia|cbn; lia]]).
    assert (HB0 : cellA M2 0x13c618 8 4096) by (apply TC; [lia|cbn; lia|apply GI; cbn; lia|exact I1]).
    assert (HB16 : cellA M2 (0x13c618 + 16) 8 parr) by (apply TC; [lia|cbn; lia|apply GI; cbn; lia|exact I8]).
    replace ((log ++ [AMmapNull msz r]) ++ [AMmapFixed (parr + 8 * 0) 131072]) with (log ++ art_sec_events msz r parr 0 false) by (unfold art_sec_events; rewrite <- app_assoc; reflexivity).
    apply (HK r regs' MF Pr).
    + exact E10.
    + exact E2.
    + exact E1.
    + intros x Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        first [ exact E8 | exact E9 | exact E18 | exact E19 | exact E20 | exact E21 | exact E22 | exact E23 | exact E24 | exact E25
              | (rewrite E3; unfold R2; gres; rewrite B3; apply XK; inl) | (rewrite E4; symmetry; exact H4)
              | (rewrite E26; unfold R2; gres; rewrite B26; apply XK; inl) | (rewrite E27; unfold R2; gres; rewrite B27; apply XK; inl) ].
    + eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G12|exact G2F].
    + eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A01 A1F)|].
      unfold art_sec_fp, SB. intros z. clear - SH2 SH3 Hq1 Emsz. fold lo hi. intros Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia.
    + intros x b Hx Nx Mx. pose proof (bv_unsigned_in_range 64 x) as Rx.
      rewrite (art_agree_pt _ _ _ x A1F).
      2:{ clear - Hx Nx SH1 SH4 Hkh APt APp APr Hq1 Emsz Hri. unfold appmem, SB, kHighMemBeg in *. cbn [art_out fst snd]. repeat split; try exact I; lia. }
      unfold M1. apply art_reveal_some. rewrite art_zfill_out by (clear - Hx SH1 SH4 APr; unfold appmem, SB, kHighMemBeg in *; lia).
      rewrite (art_agree_pt [(s - 464, 464)] M M0 x); [exact Mx| |].
      * unfold M0, art_sec_pre_mem. eapply art_agree_sub; [zagree|]. clear - Hs Hs' HHI. zsub.
      * clear - Hx SH4 Hkh. cbn [art_out fst snd]. repeat split; try exact I; lia.
    + eapply wr_grows; [eapply mem_grows_trans; [exact G12|exact G2F]|exact W1r].
    + eapply wr_grows; [eapply mem_grows_trans; [exact G12|exact G2F]|exact W1s].
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx.
      rewrite (art_agree_pt _ _ _ x A1F).
      2:{ clear - Hx AP1 Hri Art Arp APr SH6 SH7 Hq1 Emsz Hrm Hs Hs'. unfold appmem, SB, kHighMemBeg, apart in *. cbn [art_out fst snd]. repeat split; try exact I; lia. }
      unfold M1. apply art_reveal_some. apply art_zfill_in. lia.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. apply art_lock_word_release; [lia|lia|]. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + unfold MF, sec_postB_mem, sec_tail_mem. clear - AP1 AP2 AP3 AP6 AP7 AP8 AP9 AP10 AP11 Hs Hs' HHI Hkh Hr Hri Hrm Hparr Hparr' Hnch HL Ht0 Ht' Hq1 Emsz Hn HBr HBr8 HBr16 HBlk HB0 HB16 J3 J4 J5; zcell.
    + replace parr with (parr + 8 * 0) at 1 by lia. eapply wr_grows; [exact G2F|]. unfold M2. apply wr_zfill; lia.
Qed.
End Spec.
