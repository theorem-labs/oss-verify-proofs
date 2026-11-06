(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
 BnModel BnMath BnMem BnDefs LibIface BnP_add BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_frame
 BnB_lib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record adsG (o buf len sp sp1 FS p2 g og bg0 bgl : Z) : Prop := AdsG {
  g_o1 : APP o 516; g_o2 : o + 516 <= HIE; g_o8 : o = 8 * og;
  g_b1 : APP buf len; g_b2 : buf + len <= HIE; g_len : 1 <= len <= 780;
  g_bg0 : 8 * bg0 <= buf < 8 * bg0 + 8; g_bgl : 8 * bgl <= buf + len - 1 < 8 * bgl + 8;
  g_sp1 : KHI + 656 <= sp; g_sp2 : sp <= HIE;
  g_s1a : sp - 400 <= sp1; g_s1b : sp1 <= sp - 384; g_s1m : exists q, sp1 = 32 * q;
  g_fs1 : APP FS FS_LEN; g_fs2 : FS + FS_LEN <= HIE; g_fs4 : exists q, FS = 4096 * q; g_p2 : 0 <= p2 < 512;
  g_gF : FS + 5279744 + p2 * 2048 = 8 * (g - SHA);
  g_osp : o + 516 <= sp - 656 \/ sp <= o;
  g_bsp : buf + len <= sp - 656 \/ sp <= buf;
  g_bo : buf + len <= o \/ o + 516 <= buf;
  g_oF : o + 516 <= FS + 5279744 + p2 * 2048 \/ FS + 5279744 + p2 * 2048 + 2048 <= o;
  g_bF : buf + len <= FS + 5279744 + p2 * 2048 \/ FS + 5279744 + p2 * 2048 + 2048 <= buf;
  g_spFS : sp <= FS \/ FS + FS_LEN <= sp - 656;
  g_ohd : FS + 36864 <= o /\ o + 516 <= FS + FS_LEN;
  g_bhd : buf + len <= FS + 40 \/ FS + 48 <= buf;
  g_bh2 : buf + len <= FS + 35840 \/ FS + 36352 <= buf }.

Ltac geom GG :=
  destruct GG as [Go1 Go2 Go8 Gb1 Gb2 Glen Gbg0 Gbgl Gsp1 Gsp2 Gs1a Gs1b Gs1m Gfs1 Gfs2 Gfs4 Gp2 GgF Dosp Dbsp Dbo DoF DbF DspFS Dohd Dbhd Dbh2];
  unfold FS_LEN in *;
  move Dbo after Dbh2; move Dbsp after Dbo; move DspFS after Dbsp; move DoF after DspFS; move Dosp after DoF;
  hide Dosp; hide Dbsp; hide Dbo; hide DoF; hide DbF; hide DspFS; hide Dbhd; hide Dbh2.

Ltac flia := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
Ltac slia := cbn [fst snd]; repeat match goal with |- _ /\ _ => split end; flia.
Ltac flia0 := first [ lia | match goal with H : hide _ |- _ => unfold hide in H; lia end | (unfold hide in *; lia) ].
#[local] Ltac flia ::= lf_once flia0.

(* [comment removed for export] *)
Ltac ptrchkA :=
  lazymatch goal with
  | |- Z.lxor _ _ <> _ =>
      repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b); [exfalso; lia|] end;
      vm_compute; discriminate
  end.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (o buf len sp sp1 FS p2 g og bg0 bgl : Z) (ds : list Z).
Hypothesis GG : adsG o buf len sp sp1 FS p2 g og bg0 bgl.
Hypothesis Hds : length ds = Z.to_nat len.
Hypothesis DOK : digits_ok ds.
(* [comment removed for export] *)
Hypothesis add_B_h : forall regs m (o q sp : Z) (ret : word) (l ol : list Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 q -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  bn_at SEGS_B m o (BN l 0) -> bn_at SEGS_B m q (BN ol 0) -> ok l -> ok ol -> zlen l <= 126 -> 1 <= zlen ol <= 3 ->
  KHI + 128 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> APP q 516 -> q + 516 <= HIE -> o mod 8 = 0 -> q mod 8 = 0 ->
  (q + 516 <= o \/ o + 516 <= q) -> (o + 516 <= sp - 128 \/ sp <= o) -> (q + 516 <= sp - 128 \/ sp <= q) ->
  shcellsB m -> objshB m o -> objshB m q ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 128)) 128 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aab04) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_B m' o (BN (add_l 0 l ol) 0)
    /\ unch m m' [(o, o + 516); (sp - 128, sp)] /\ mem_grows m m'.

#[local] Abbreviation F := (FS + 5279744 + p2 * 2048).
#[local] Abbreviation G := g.

(* [comment removed for export] *)
Definition NS : list (Z * Z) := [(o, o + 516); (FS + 40, FS + 48); (FS + 35840 + p2, FS + 35840 + p2 + 1); (F, F + 1344); (G, G + 256)].

Ltac inr0 H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
Ltac inr H tac := lf_once ltac:(inr0 H tac).
Ltac unch_ns U :=
  eapply unch_widen; [exact U|];
  let rg := fresh "rg" in let H := fresh "Hrg" in
  intros rg H; unfold NS; cbn [fst snd];
  inr H ltac:(first [ eexists; split; [left; reflexivity | cbn; lia]
                    | eexists; split; [right; left; reflexivity | cbn; lia]
                    | eexists; split; [right; right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 4 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 5 right; left; reflexivity | cbn; lia]
                    | unfold hide in *;
                      first [ eexists; split; [left; reflexivity | cbn; lia]
                    | eexists; split; [right; left; reflexivity | cbn; lia]
                    | eexists; split; [right; right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 4 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 5 right; left; reflexivity | cbn; lia] ] ]).

(* [comment removed for export] *)
Definition digs (m : word -> option byte) : Prop := forall k, (k < length ds)%nat -> cellN SEGS_B m (buf + Z.of_nat k) 1 (nth k ds 0).
Definition dsh (m : word -> option byte) : Prop := forall q, bg0 <= q <= bgl -> cellN SEGS_B m (SHA + q) 1 0.
Definition AMB (m : word -> option byte) : Prop :=
  shcellsB m /\ mscellsB m /\ arr32 SEGS_B m 145376 five_tbl /\ tblshB m /\ objshB m o /\ digs m /\ dsh m
  /\ cellN SEGS_B m 66408 8 7450580596923828125.
Definition ambr (r : Z * Z) : Prop :=
  (2 ^ 32 <= fst r \/ (IMG <= fst r /\ snd r <= LOSH) \/ (LSLO <= fst r /\ snd r <= LSHI)) /\ (snd r <= buf \/ buf + len <= fst r)   (* [comment removed for export] *)
  /\ (snd r <= SHA + og \/ SHA + og + 64 <= fst r)
  /\ (snd r <= SHA + bg0 \/ SHA + bgl + 1 <= fst r).

#[using="sp sp1 FS p2 g GG Hds"] Lemma AMB_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> ambr r) -> AMB m -> AMB m'.
Proof.
  intros m m' rs U HR (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). geom GG. unhide.
  assert (HH : forall r, In r rs -> highr r) by (intros r Hr; exact (proj1 (HR r Hr))).
  split; [eapply shcellsB_unch'; [exact U | exact HH | exact A1]|].
  split; [eapply mscellsB_unch; [exact U | exact HH | exact A2]|].
  split; [eapply five_tblB_unch; [exact U | exact HH | exact A3]|].
  split; [eapply tblshB_unch; [exact U | exact HH | exact A4]|].
  split.
  { intros k Hk. eapply cellN_unch; [exact U | (try clear - o buf len sp FS p2 g og ds Hds Go1 Go8 Gb1 Glen Gsp1 Gfs1 Gp2 GgF DbF Dohd Dbhd Dbh2 Dbo DspFS DoF Dosp k Hk; lia) | cbn; (try clear - o buf len sp FS p2 g og ds Hds Go1 Go2 Go8 Gb2 Glen Gsp2 Gfs2 Gp2 GgF Dohd Dbhd Dbh2 Dbsp DspFS k Hk; lia) | | apply A5; exact Hk].
    intros r Hr. destruct (HR r Hr) as (_ & _ & X & _). cbn. (try clear - o buf len sp FS p2 g og ds Hds Go1 Go8 Gb1 Glen Gsp1 Gfs1 Gp2 GgF DbF Dohd Dbhd Dbh2 Dbo Dbsp DspFS DoF Dosp k Hk r X; lia). }
  split.
  { intros k Hk. rewrite Hds in Hk. eapply cellN_unch; [exact U | (try clear - o buf len sp FS p2 g og ds Hds Go1 Go8 Gb1 Glen Gsp1 Gfs1 Gp2 GgF Dohd DspFS DoF Dosp k Hk; lia) | cbn; (try clear - buf len sp FS p2 ds Hds Gb2 Glen Gsp2 Gfs2 Gp2 DspFS k Hk; lia) | | apply A6; rewrite Hds; exact Hk].
    intros r Hr. destruct (HR r Hr) as (_ & X & _ & _). cbn. (try clear - o buf len sp FS p2 g og ds Hds Go1 Go8 Gb1 Glen Gsp1 Gfs1 Gp2 GgF DbF Dohd Dbhd Dbh2 Dbo Dbsp DspFS DoF Dosp k Hk r X; lia). }
  split.
  { intros q Hq. eapply cellN_unch; [exact U | (try clear - o buf len sp FS p2 g og bg0 bgl Go1 Go8 Gb1 Glen Gbg0 Gsp1 Gfs1 Gp2 GgF Dohd Dbhd Dbh2 Dbo DspFS Dosp q Hq; lia) | cbn; (try clear - buf len sp FS p2 bg0 bgl Gb2 Gbgl Gsp2 Gfs2 Gp2 DspFS q Hq; lia) | | apply A7; exact Hq].
    intros r Hr. destruct (HR r Hr) as (_ & _ & _ & X). cbn. (try clear - o buf len sp FS p2 g og bg0 bgl Go1 Go8 Gb1 Glen Gsp1 Gfs1 Gp2 GgF DbF Dohd Dbhd Dbh2 Dbo Dbsp DspFS DoF Dosp q Hq r X; lia). }
  eapply cellN_low_unchB; [exact U | exact HH | lia | cbn; lia | exact A8].
Qed.

(* [comment removed for export] *)
Definition SL1 (m : word -> option byte) : Prop :=
  cellN SEGS_B m (sp1 + 240) 8 (G + 86) /\ cellN SEGS_B m (sp1 + 64) 8 G /\ cellN SEGS_B m (sp1 + 24) 8 (G + 4)
  /\ cellN SEGS_B m (sp1 + 48) 8 (SHA + og) /\ cellN SEGS_B m (sp1 + 32) 8 (SHA + og) /\ cellN SEGS_B m (sp1 + 40) 8 (o + 2).
Definition sl1r (r : Z * Z) : Prop := snd r <= sp1 + 24 \/ sp1 + 248 <= fst r.
(* [comment removed for export] *)
Definition SL2 (m : word -> option byte) : Prop :=
  cellN SEGS_B m (sp1 + 16) 8 F /\ cellN SEGS_B m (sp1 + 8) 8 F /\ cellN SEGS_B m (sp1 + 232) 8 (F + 688)
  /\ cellN SEGS_B m (sp1 + 56) 8 (F + 692) /\ cellN SEGS_B m (sp1 + 72) 8 o
  /\ cellN SEGS_B m (sp1 + 224) 8 (18446744073709551615 - buf)
  /\ (forall k, 1 <= k <= 18 -> cellN SEGS_B m (sp1 + 224 - 8 * k) 8 (buf + k)).
Definition sl2r (r : Z * Z) : Prop := snd r <= sp1 + 8 \/ sp1 + 240 <= fst r.
(* [comment removed for export] *)
Definition SAV (m : word -> option byte) (vs : list Z) : Prop :=
  forall k, (k < 13)%nat -> cellN SEGS_B m (sp - 8 - 8 * Z.of_nat k) 8 (nth k vs 0).
Definition savr (r : Z * Z) : Prop := snd r <= sp - 104 \/ sp <= fst r.

#[using="buf len sp FS p2 bg0 bgl GG"] Lemma SL1_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> sl1r r) -> SL1 m -> SL1 m'.
Proof.
  clear Hds DOK.
  intros m m' rs U HR (A1 & A2 & A3 & A4 & A5 & A6). geom GG. unfold SL1.
  repeat match goal with |- _ /\ _ => split end;
  (eapply cellN_unch; [exact U | lia | cbn; lia | | eassumption]);
  intros r Hr; specialize (HR r Hr); unfold sl1r in HR; cbn; lia.
Qed.
#[using="len sp g og bg0 bgl GG"] Lemma SL2_unch : forall m m' rs, unch m m' rs -> (forall r, In r rs -> sl2r r) -> SL2 m -> SL2 m'.
Proof.
  clear Hds DOK.
  intros m m' rs U HR (A1 & A2 & A3 & A4 & A5 & A6 & A7). geom GG. unfold SL2.
  repeat match goal with |- _ /\ _ => split end;
  try ((eapply cellN_unch; [exact U | lia | cbn; lia | | eassumption]);
  intros r Hr; specialize (HR r Hr); unfold sl2r in HR; cbn; lia).
  intros k Hk. eapply cellN_unch; [exact U | lia | cbn; lia | | apply A7; exact Hk].
  intros r Hr; specialize (HR r Hr); unfold sl2r in HR; cbn; lia.
Qed.
#[using="o buf len sp1 FS p2 g og bg0 bgl GG"] Lemma SAV_unch : forall m m' rs vs, unch m m' rs -> (forall r, In r rs -> savr r) -> SAV m vs -> SAV m' vs.
Proof.
  clear Hds DOK.
  intros m m' rs vs U HR A k Hk. geom GG.
  eapply cellN_unch; [exact U | lia | cbn; lia | | apply A; exact Hk].
  intros r Hr; specialize (HR r Hr); unfold savr in HR; cbn; lia.
Qed.

(* [comment removed for export] *)
Definition WIN (m : word -> option byte) : Prop :=
  mem_def m (sp - 656) 656 /\ mem_def m o 516 /\ mem_def m F 2048 /\ mem_def m G 256.
#[using="Type"] Lemma WIN_grows : forall m m', mem_grows m m' -> WIN m -> WIN m'.
Proof.
  clear GG Hds DOK.
  intros m m' Hgr (A & B & C & D). unfold WIN.
  repeat split; (eapply mem_def_grows; [exact Hgr | assumption]).
Qed.

Ltac rngs := let rg := fresh "rg" in let H := fresh "Hrg" in
  intros rg H; unfold ambr, sl1r, sl2r, savr, highr; inr H ltac:(slia).

(* [comment removed for export] *)
#[using="Type"] Lemma bn_ctor_hi : forall m a x, 0 <= a -> a + 4 <= M64 -> x = a + 2 ->
  cellN SEGS_B (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 0))) x 2 0.
Proof. clear GG Hds DOK. intros m a x Ha Hb ->. exact (proj2 (bn_ctor_store SEGS_B m a Ha Hb)). Qed.
Ltac cellx2 :=
  lazymatch goal with
  | |- cellN _ (wbytes _ (Z_to_bv 64 _) (word_to_le_bytes _ _)) _ _ _ =>
      first
        [ assumption
        | apply bn_ctor_hi; [lia | zwidth; lia | lia]
        | apply cellN_store_same';
          [ cbn; lia | lia | zwidth; lia
          | rewrite ?u_Z2bv64; zwidth;
            first [ reflexivity | lia
                  | rewrite (Z.mod_small _ 18446744073709551616) by lia; first [apply Z.mod_small; lia | rewrite Z.mod_small by lia; lia | idtac]
                  | idtac ] ]
        | apply cellN_store_skip; [ flia | zwidth; flia | flia | zwidth; flia | zwidth; flia | cellx2 ]
        | idtac ]
  | |- cellN _ _ _ _ _ => first [assumption | eassumption | idtac]
  end.

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AA1_KEEP : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27].

(* [comment removed for export] *)
Abbreviation aa1_pins := [(9%bv : reg, ZV 33); (2%bv : reg, ZV 33); (25%bv : reg, ZV 32); (23%bv : reg, ZV 36); (19%bv : reg, ZL 268435455)].
Abbreviation aa1_kn := [KC (ZV 33) 64 8 (ZV 34); KC (ZV 33) 232 8 (ZAdd (ZV 35) (ZL 688)); KC (ZV 33) 56 8 (ZAdd (ZV 35) (ZL 692))].
Abbreviation aa1_uvi dlo dhi := [Some (IMG, HIE - 516); Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256); Some (IMG, HIE - 2048); Some (dlo, dhi)].
Ltac aa1_run dlo dhi regs m rom d :=
  zx_run SEGS_B constr:(CTX (vi_regs ++ aa1_uvi dlo dhi) aa1_kn [KW (ZV 34) 150 151; KW (ZV 35) 688 1204])
    40%nat [0x0aab04] (SCR [] []) constr:(aa1_pins) [o; sp1; g; FS + 5279744 + p2 * 2048; d] constr:(aa1_uvi dlo dhi) regs m rom 0x0aa2d8.

#[using="len GG Hds add_B_h"] Lemma au64add_B1 : forall regs m (d : Z) (l : list Z),
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 2%bv = Z_to_bv 64 sp1 -> getr regs 25%bv = Z_to_bv 64 o ->
  getr regs 23%bv = Z_to_bv 64 d -> getr regs 19%bv = Z_to_bv 64 MASK ->
  1 <= d < 2 ^ 64 -> bn_at SEGS_B m o (BN l 0) -> ok l -> zlen l <= 126 ->
  AMB m -> SL1 m -> SL2 m -> WIN m ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa2cc) m rom) (mkst regs' (Z_to_bv 64 0x0a9f14) m' rom)
    /\ bn_at SEGS_B m' o (BN (add_l 0 l (chunks 3 d)) 0)
    /\ keeps AA1_KEEP regs regs'
    /\ unch m m' ((sp1 - 128, sp1) :: NS) /\ mem_grows m m'.
Proof.
  intros regs m d l R9 R2 R25 R23 R19 Hd Hbn Hok Hlen AM L1 L2 W.
  pose proof AM as AM0. pose proof L1 as L10. pose proof L2 as L20.
  destruct AM as (SC & MC & TBL & TSH & OSH & DG & DSH & K27C). destruct L1 as (L240 & L64 & L24 & L48 & L32 & L40).
  destruct L2 as (L16 & L8 & L232 & L56 & L72 & L224 & LT). destruct W as (Wsp & Wo & WF & WG).
  geom GG. unfold MASK in R19.
  pose proof (chunks_spec 3 d ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & Hcok & _ & Hck).
  assert (Hcl : 1 <= zlen (chunks 3 d) <= 3).
  { split; [|exact Hck]. destruct (chunks 3 d) eqn:Ec; [|rewrite zlen_cons; pose proof (zlen_nonneg l0); lia].
    exfalso. assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
    destruct CASES as [H|[H|H]]; [rewrite chunks_1 in Ec by exact H | rewrite chunks_2 in Ec by exact H | rewrite chunks_3 in Ec by exact H]; discriminate. }
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) [KC (ZV 32) 240 8 (ZAdd (ZV 33) (ZL 86))] (@nil kwin))
    10%nat [0x78470] (SCR [] []) constr:([(9%bv : reg, ZV 32)]) [sp1; G] constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) regs m rom 0x0aa2cc.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L240; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (1%bv : reg) as A1.
  rename ZM into M1. clear ZE ZR ZF.
  destruct (setsh_B rom false regs1 m (G + 86) 64 (Z_to_bv 64 0x0aa2d8)) as (regs2 & M2 & K2).
  { rewrite A10; f_equal; lia. } { exact A11. } { exact A1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [exact WG|]. zwidth. lia. } { exact MC. }
  cbn [negb] in M2.
  set (m1 := wbytes m (Z_to_bv 64 (G + 86)) (repeat (Z_to_bv 8 0) (Z.to_nat 64))) in M2.
  assert (U01 : unch m m1 [(G + 86, G + 150)]).
  { unfold m1. eapply (unch_store_bs m (G + 86)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G01 : mem_grows m m1) by (unfold m1; apply grows_store).
  assert (OB1 : objshB m1 (F + 688)).
  { intros k Hk. unfold m1. eapply cellN_byte; [| lia | lia | lia].
    replace (SHA + (F + 688) / 8 + k) with (g + 86 + k) by lia.
    apply mem_byte_repeat_in; rewrite ?repeat_length; try lia. reflexivity. }
  pose proof (SL1_unch m m1 _ U01 ltac:(rngs) L10) as (L240' & L64' & L24' & L48' & L32' & L40').
  pose proof (SL2_unch m m1 _ U01 ltac:(rngs) L20) as (L16' & L8' & L232' & L56' & L72' & L224' & LT').
  pose proof (WIN_grows m m1 G01 (conj Wsp (conj Wo (conj WF WG)))) as (Wsp1 & Wo1 & WF1 & WG1).
  assert (B9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 9 ltac:(in_list)) | kept K1 9 R9]).
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 2 ltac:(in_list)) | kept K1 2 R2]).
  assert (B25 : getr regs2 25%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 25 ltac:(in_list)) | kept K1 25 R25]).
  assert (B23 : getr regs2 23%bv = Z_to_bv 64 d) by (etransitivity; [exact (K2 23 ltac:(in_list)) | kept K1 23 R23]).
  assert (B19 : getr regs2 19%bv = Z_to_bv 64 268435455) by (etransitivity; [exact (K2 19 ltac:(in_list)) | kept K1 19 R19]).
  assert (K12 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs2).
  { eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]. }
  assert (M12 : msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa2cc) m rom) (mkst regs2 (Z_to_bv 64 0x0aa2d8) m1 rom)).
  { eapply msteps_trans; [exact M1 | exact M2]. }
  clear M1 M2 K1 K2 A10 A11 A1 regs1.
  (* [comment removed for export] *)
  assert (CONT : forall regs3 m2,
    msteps SEGS_B (mkst regs2 (Z_to_bv 64 0x0aa2d8) m1 rom) (mkst regs3 (Z_to_bv 64 0x0aab04) m2 rom) ->
    getr regs3 10%bv = Z_to_bv 64 o -> getr regs3 11%bv = Z_to_bv 64 (F + 688) -> getr regs3 2%bv = Z_to_bv 64 sp1 ->
    getr regs3 1%bv = Z_to_bv 64 0x0aa31c -> getr regs3 9%bv = Z_to_bv 64 sp1 ->
    bn_at SEGS_B m2 (F + 688) (BN (chunks 3 d) 0) -> objshB m2 (F + 688) ->
    keeps AA1_KEEP regs regs3 -> unch m1 m2 [(G + 150, G + 151); (F + 688, F + 1204)] -> mem_grows m1 m2 ->
    exists regs' m',
      msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa2cc) m rom) (mkst regs' (Z_to_bv 64 0x0a9f14) m' rom)
      /\ bn_at SEGS_B m' o (BN (add_l 0 l (chunks 3 d)) 0)
      /\ keeps AA1_KEEP regs regs'
      /\ unch m m' ((sp1 - 128, sp1) :: NS) /\ mem_grows m m').
  { intros regs3 m2 M3 C10 C11 C2 C1 C9 Hq OBq K3 U12 G12.
    assert (U02 : unch m m2 [(G + 86, G + 151); (F + 688, F + 1204)]).
    { eapply unch_trans; [| eapply unch_widen; [exact U12|]].
      - eapply unch_widen; [exact U01|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity | cbn; lia].
      - intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]]. }
    assert (G02 : mem_grows m m2) by (eapply mem_grows_trans; [exact G01 | exact G12]).
    pose proof (AMB_unch m m2 _ U02 ltac:(rngs) AM0) as AM2. pose proof AM2 as (SC2 & MC2 & _ & _ & OSH2 & _ & _ & _).
    pose proof (SL1_unch m m2 _ U02 ltac:(rngs) L10) as L12.
    pose proof (WIN_grows m m2 G02 (conj Wsp (conj Wo (conj WF WG)))) as (Wsp2 & Wo2 & WF2 & WG2).
    assert (Hbo2 : bn_at SEGS_B m2 o (BN l 0)).
    { eapply bn_at_unch; [exact U02 | lia | cbn; lia | | exact Hbn]. intros r Hr. inr Hr ltac:(slia). }
    destruct (add_B_h regs3 m2 o (F + 688) sp1 (Z_to_bv 64 0x0aa31c) l (chunks 3 d)) as (regs4 & m3 & M4 & K4 & Hbn4 & U34 & G34).
    { exact C10. } { exact C11. } { exact C2. } { exact C1. } { vm_compute. reflexivity. }
    { exact Hbo2. } { exact Hq. } { exact Hok. } { exact Hcok. } { exact Hlen. } { exact Hcl. }
    { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
    { flia. } { flia. } { flia. }
    { exact SC2. } { exact OSH2. } { exact OBq. }
    { eapply store_ok_of_def_in; [exact Wo2|]. zwidth. lia. } { eapply store_ok_of_def_in; [exact Wsp2|]. zwidth. lia. }
    pose proof (AMB_unch m2 m3 _ U34 ltac:(rngs) AM2) as AM3. pose proof AM3 as (_ & MC3 & _).
    pose proof (SL1_unch m2 m3 _ U34 ltac:(rngs) L12) as L13. pose proof L13 as (N240 & _).
    pose proof (WIN_grows m2 m3 G34 (conj Wsp2 (conj Wo2 (conj WF2 WG2)))) as (Wsp3 & Wo3 & WF3 & WG3).
    assert (D9 : getr regs4 9%bv = Z_to_bv 64 sp1) by (kept K4 9 C9).
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) [KC (ZV 32) 240 8 (ZAdd (ZV 33) (ZL 86))] (@nil kwin))
      10%nat [0x78590] (SCR [] []) constr:([(9%bv : reg, ZV 32)]) [sp1; G] constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) regs4 m3 rom 0x0aa31c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 N240; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
    assert (K5 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs4 regs5) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (10%bv : reg) as E10. zx_reg ZR (11%bv : reg) as E11. zx_reg ZR (1%bv : reg) as E1.
    rename ZM into M5. clear ZE ZR ZF.
    destruct (setsh_B rom true regs5 m3 (G + 86) 65 (Z_to_bv 64 0x0aa328)) as (regs6 & M6 & K6).
    { rewrite E10; f_equal; lia. } { exact E11. } { exact E1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
    { eapply store_ok_of_def_in; [exact WG3|]. zwidth. lia. } { exact MC3. }
    cbn [negb] in M6.
    set (m4 := wbytes m3 _ _) in M6.
    assert (U45 : unch m3 m4 [(G + 86, G + 151)]).
    { unfold m4. eapply (unch_store_bs m3 (G + 86)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
    assert (G45 : mem_grows m3 m4) by (unfold m4; apply grows_store).
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 3%nat [0x0a9f14] (SCR [] []) constr:(@nil (reg * zx))
      (@nil Z) constr:(@nil (option (Z * Z))) regs6 m4 rom 0x0aa328.
    zx_use2 ZXB ltac:(exact I) ltac:(exact I) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs7.
    eexists regs7, m4. split.
    { eapply msteps_trans; [exact M12|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
      eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6 | exact ZM]. }
    split.
    { eapply bn_at_unch; [exact U45 | lia | cbn; lia | | exact Hbn4]. intros r Hr. inr Hr ltac:(slia). }
    split.
    { eapply keeps_trans; [exact K3|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity|].
      eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
    split.
    { eapply unch_trans; [unch_ns U02|]. eapply unch_trans; [unch_ns U34 | unch_ns U45]. }
    eapply mem_grows_trans; [exact G02|]. eapply mem_grows_trans; [exact G34 | exact G45]. }
  (* [comment removed for export] *)
  assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
  destruct CASES as [Hv1 | [Hv2 | Hv3]].
  - rewrite chunks_1 in * by exact Hv1. unfold B in *.
    aa1_run 1 (2 ^ 28 - 1) regs2 m1 rom d.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L64'; kc1 L232'; kc1 L56'; exact I) ltac:(kwd WG1; kwd WF1; exact I) ltac:(idtac; zx_scs ltac:(flia)). zx_name regs3.
    zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (2%bv : reg) as C2. zx_reg ZR (1%bv : reg) as C1. zx_reg ZR (9%bv : reg) as C9.
    assert (K3 : keeps AA1_KEEP regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
    clear ZE ZR ZF.
    eapply CONT; [exact ZM | rewrite C10; reflexivity | rewrite C11; f_equal; lia | rewrite C2; reflexivity | rewrite C1; reflexivity | rewrite C9; reflexivity | |
                 | exact K3 | clear ZM CONT; unchx | growsx].
    + clear ZM CONT. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [d])) with 1.
      split; [cellx2|split; [cellx2|split; [|lia]]].
      apply arr32_store_other; zwidth; try lia.
      intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. replace (F + 688 + 4 + 4 * Z.of_nat 0) with (F + 692) by lia. cellx2.
    + clear ZM CONT. eapply (objshB_unch2 m1 _ [(g + 150, g + 151); (F + 688, F + 1204)]); [unchx | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OB1].
  - rewrite chunks_2 in * by exact Hv2. unfold B in *.
    aa1_run (2 ^ 28) (2 ^ 56 - 1) regs2 m1 rom d.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L64'; kc1 L232'; kc1 L56'; exact I) ltac:(kwd WG1; kwd WF1; exact I) ltac:(idtac; zx_scs ltac:(flia)). zx_name regs3.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 1 <= d / 268435456 < 268435456) by lia.
    change (2 ^ 28) with 268435456 in *.
    zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (2%bv : reg) as C2. zx_reg ZR (1%bv : reg) as C1. zx_reg ZR (9%bv : reg) as C9.
    assert (K3 : keeps AA1_KEEP regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
    clear ZE ZR ZF. change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456) as c2 eqn:E2. clear E1 E2.
    eapply CONT; [exact ZM | rewrite C10; reflexivity | rewrite C11; f_equal; lia | rewrite C2; reflexivity | rewrite C1; reflexivity | rewrite C9; reflexivity | |
                 | exact K3 | clear ZM CONT; unchx | growsx].
    + clear ZM CONT. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2])) with 2.
      split; [cellx2|split; [cellx2|split; [|lia]]].
      apply arr32_store_other; zwidth; try lia.
      intros i Hi. cbn in Hi. destruct i as [|[|]]; [| |lia]; cbn [nth]; zwidth.
      * replace (F + 688 + 4 + 4 * 0) with (F + 692) by lia. cellx2.
      * replace (F + 688 + 4 + 4 * 1) with (F + 696) by lia. cellx2.
    + clear ZM CONT. eapply (objshB_unch2 m1 _ [(g + 150, g + 151); (F + 688, F + 1204)]); [unchx | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OB1].
  - rewrite chunks_3 in * by exact Hv3. unfold B in *.
    aa1_run (2 ^ 56) (2 ^ 64 - 1) regs2 m1 rom d.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L64'; kc1 L232'; kc1 L56'; exact I) ltac:(kwd WG1; kwd WF1; exact I) ltac:(idtac; zx_scs ltac:(flia)). zx_name regs3.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 0 <= d / 268435456 mod 268435456 < 268435456) by lia.
    assert (HB3 : 1 <= d / 268435456 / 268435456 < 256) by lia.
    change (2 ^ 28) with 268435456 in *.
    zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (2%bv : reg) as C2. zx_reg ZR (1%bv : reg) as C1. zx_reg ZR (9%bv : reg) as C9.
    assert (K3 : keeps AA1_KEEP regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
    clear ZE ZR ZF. change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456 mod 268435456) as c2 eqn:E2.
    remember (d / 268435456 / 268435456) as c3 eqn:E3. clear E1 E2 E3.
    eapply CONT; [exact ZM | rewrite C10; reflexivity | rewrite C11; f_equal; lia | rewrite C2; reflexivity | rewrite C1; reflexivity | rewrite C9; reflexivity | |
                 | exact K3 | clear ZM CONT; unchx | growsx].
    + clear ZM CONT. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2; c3])) with 3.
      split; [cellx2|split; [cellx2|split; [|lia]]].
      apply arr32_store_other; zwidth; try lia.
      intros i Hi. cbn in Hi. destruct i as [|[|[|]]]; [| | |lia]; cbn [nth]; zwidth.
      * replace (F + 688 + 4 + 4 * 0) with (F + 692) by lia. cellx2.
      * replace (F + 688 + 4 + 4 * 1) with (F + 696) by lia. cellx2.
      * replace (F + 688 + 4 + 4 * 2) with (F + 700) by lia. cellx2.
    + clear ZM CONT. eapply (objshB_unch2 m1 _ [(g + 150, g + 151); (F + 688, F + 1204)]); [unchx | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OB1].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AA2_KEEP : list Z := [2; 3; 4; 8; 9; 18; 20; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Abbreviation aa2_pins := [(9%bv : reg, ZV 33); (2%bv : reg, ZV 33); (25%bv : reg, ZV 32); (19%bv : reg, ZV 36); (21%bv : reg, ZL 268435455); (23%bv : reg, ZAdd (ZV 35) (ZL 32))].
Abbreviation aa2_kn := [KC (ZV 33) 64 8 (ZV 34)].
Abbreviation aa2_uvi dlo dhi := [Some (IMG, HIE - 516); Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256); Some (IMG, HIE - 2048); Some (dlo, dhi)].
Ltac aa2_run dlo dhi regs m rom d :=
  zx_run SEGS_B constr:(CTX (vi_regs ++ aa2_uvi dlo dhi) aa2_kn [KW (ZV 34) 68 69; KW (ZV 35) 32 548])
    40%nat [0x0aab04] (SCR [] []) constr:(aa2_pins) [o; sp1; g; FS + 5279744 + p2 * 2048; d] constr:(aa2_uvi dlo dhi) regs m rom 0x0aa4c0.

#[using="len GG Hds add_B_h"] Lemma au64add_B2 : forall regs m (d : Z) (l : list Z),
  getr regs 9%bv = Z_to_bv 64 sp1 -> getr regs 2%bv = Z_to_bv 64 sp1 -> getr regs 25%bv = Z_to_bv 64 o ->
  getr regs 19%bv = Z_to_bv 64 d -> getr regs 23%bv = Z_to_bv 64 (F + 32) ->
  1 <= d < 2 ^ 64 -> bn_at SEGS_B m o (BN l 0) -> ok l -> zlen l <= 126 ->
  AMB m -> SL1 m -> WIN m ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa4a8) m rom) (mkst regs' (Z_to_bv 64 0x0aa50c) m' rom)
    /\ bn_at SEGS_B m' o (BN (add_l 0 l (chunks 3 d)) 0)
    /\ keeps AA2_KEEP regs regs'
    /\ unch m m' ((sp1 - 128, sp1) :: NS) /\ mem_grows m m'.
Proof.
  intros regs m d l R9 R2 R25 R19 R23 Hd Hbn Hok Hlen AM L1 W.
  pose proof AM as AM0. pose proof L1 as L10.
  destruct AM as (SC & MC & TBL & TSH & OSH & DG & DSH & K27C). destruct L1 as (L240 & L64 & L24 & L48 & L32 & L40).
  destruct W as (Wsp & Wo & WF & WG).
  geom GG.
  pose proof (chunks_spec 3 d ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & Hcok & _ & Hck).
  assert (Hcl : 1 <= zlen (chunks 3 d) <= 3).
  { split; [|exact Hck]. destruct (chunks 3 d) eqn:Ec; [|rewrite zlen_cons; pose proof (zlen_nonneg l0); lia].
    exfalso. assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
    destruct CASES as [H|[H|H]]; [rewrite chunks_1 in Ec by exact H | rewrite chunks_2 in Ec by exact H | rewrite chunks_3 in Ec by exact H]; discriminate. }
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) [KC (ZV 32) 24 8 (ZAdd (ZV 33) (ZL 4))] (@nil kwin))
    10%nat [0x78470] (SCR [] []) constr:([(9%bv : reg, ZV 32)]) [sp1; G] constr:([Some (KHI + 256, HIE - 384); Some (SHA, KHI - 256)]) regs m rom 0x0aa4a8.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L24; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (1%bv : reg) as A1.
  zx_reg ZR (21%bv : reg) as A21. zx_reg ZR (22%bv : reg) as A22.
  rename ZM into M1. clear ZE ZR ZF.
  destruct (setsh_B rom false regs1 m (G + 4) 64 (Z_to_bv 64 0x0aa4c0)) as (regs2 & M2 & K2).
  { rewrite A10; f_equal; lia. } { exact A11. } { exact A1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
  { eapply store_ok_of_def_in; [exact WG|]. zwidth. lia. } { exact MC. }
  cbn [negb] in M2.
  set (m1 := wbytes m (Z_to_bv 64 (G + 4)) (repeat (Z_to_bv 8 0) (Z.to_nat 64))) in M2.
  assert (U01 : unch m m1 [(G + 4, G + 68)]).
  { unfold m1. eapply (unch_store_bs m (G + 4)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
  assert (G01 : mem_grows m m1) by (unfold m1; apply grows_store).
  assert (OB1 : objshB m1 (F + 32)).
  { intros k Hk. unfold m1. eapply cellN_byte; [| lia | lia | lia].
    replace (SHA + (F + 32) / 8 + k) with (g + 4 + k) by lia.
    apply mem_byte_repeat_in; rewrite ?repeat_length; try lia. reflexivity. }
  pose proof (SL1_unch m m1 _ U01 ltac:(rngs) L10) as (L240' & L64' & L24' & L48' & L32' & L40').
  pose proof (WIN_grows m m1 G01 (conj Wsp (conj Wo (conj WF WG)))) as (Wsp1 & Wo1 & WF1 & WG1).
  assert (B9 : getr regs2 9%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 9 ltac:(in_list)) | kept K1 9 R9]).
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 sp1) by (etransitivity; [exact (K2 2 ltac:(in_list)) | kept K1 2 R2]).
  assert (B25 : getr regs2 25%bv = Z_to_bv 64 o) by (etransitivity; [exact (K2 25 ltac:(in_list)) | kept K1 25 R25]).
  assert (B19 : getr regs2 19%bv = Z_to_bv 64 d) by (etransitivity; [exact (K2 19 ltac:(in_list)) | kept K1 19 R19]).
  assert (B23 : getr regs2 23%bv = Z_to_bv 64 (F + 32)) by (etransitivity; [exact (K2 23 ltac:(in_list)) | kept K1 23 R23]).
  assert (B21 : getr regs2 21%bv = Z_to_bv 64 268435455) by (etransitivity; [exact (K2 21 ltac:(in_list)) | exact A21]).
  assert (B22 : getr regs2 22%bv = Z_to_bv 64 (G + 4)) by (etransitivity; [exact (K2 22 ltac:(in_list)) | etransitivity; [exact A22 | f_equal; lia]]).
  assert (K12 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27] regs regs2).
  { eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]. }
  assert (M12 : msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa4a8) m rom) (mkst regs2 (Z_to_bv 64 0x0aa4c0) m1 rom)).
  { eapply msteps_trans; [exact M1 | exact M2]. }
  clear M1 M2 K1 K2 A10 A11 A1 A21 A22 regs1.
  (* [comment removed for export] *)
  assert (CONT : forall regs3 m2,
    msteps SEGS_B (mkst regs2 (Z_to_bv 64 0x0aa4c0) m1 rom) (mkst regs3 (Z_to_bv 64 0x0aab04) m2 rom) ->
    getr regs3 10%bv = Z_to_bv 64 o -> getr regs3 11%bv = Z_to_bv 64 (F + 32) -> getr regs3 2%bv = Z_to_bv 64 sp1 ->
    getr regs3 1%bv = Z_to_bv 64 0x0aa500 -> getr regs3 22%bv = Z_to_bv 64 (G + 4) ->
    bn_at SEGS_B m2 (F + 32) (BN (chunks 3 d) 0) -> objshB m2 (F + 32) ->
    keeps AA2_KEEP regs regs3 -> unch m1 m2 [(G + 68, G + 69); (F + 32, F + 548)] -> mem_grows m1 m2 ->
    exists regs' m',
      msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa4a8) m rom) (mkst regs' (Z_to_bv 64 0x0aa50c) m' rom)
      /\ bn_at SEGS_B m' o (BN (add_l 0 l (chunks 3 d)) 0)
      /\ keeps AA2_KEEP regs regs'
      /\ unch m m' ((sp1 - 128, sp1) :: NS) /\ mem_grows m m').
  { intros regs3 m2 M3 C10 C11 C2 C1 C22 Hq OBq K3 U12 G12.
    assert (U02 : unch m m2 [(G + 4, G + 69); (F + 32, F + 548)]).
    { eapply unch_trans; [| eapply unch_widen; [exact U12|]].
      - eapply unch_widen; [exact U01|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity | cbn; lia].
      - intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia]]. }
    assert (G02 : mem_grows m m2) by (eapply mem_grows_trans; [exact G01 | exact G12]).
    pose proof (AMB_unch m m2 _ U02 ltac:(rngs) AM0) as AM2. pose proof AM2 as (SC2 & MC2 & _ & _ & OSH2 & _ & _ & _).
    pose proof (SL1_unch m m2 _ U02 ltac:(rngs) L10) as L12.
    pose proof (WIN_grows m m2 G02 (conj Wsp (conj Wo (conj WF WG)))) as (Wsp2 & Wo2 & WF2 & WG2).
    assert (Hbo2 : bn_at SEGS_B m2 o (BN l 0)).
    { eapply bn_at_unch; [exact U02 | lia | cbn; lia | | exact Hbn]. intros r Hr. inr Hr ltac:(slia). }
    destruct (add_B_h regs3 m2 o (F + 32) sp1 (Z_to_bv 64 0x0aa500) l (chunks 3 d)) as (regs4 & m3 & M4 & K4 & Hbn4 & U34 & G34).
    { exact C10. } { exact C11. } { exact C2. } { exact C1. } { vm_compute. reflexivity. }
    { exact Hbo2. } { exact Hq. } { exact Hok. } { exact Hcok. } { exact Hlen. } { exact Hcl. }
    { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
    { flia. } { flia. } { flia. }
    { exact SC2. } { exact OSH2. } { exact OBq. }
    { eapply store_ok_of_def_in; [exact Wo2|]. zwidth. lia. } { eapply store_ok_of_def_in; [exact Wsp2|]. zwidth. lia. }
    pose proof (AMB_unch m2 m3 _ U34 ltac:(rngs) AM2) as AM3. pose proof AM3 as (_ & MC3 & _).
    pose proof (WIN_grows m2 m3 G34 (conj Wsp2 (conj Wo2 (conj WF2 WG2)))) as (Wsp3 & Wo3 & WF3 & WG3).
    assert (D22 : getr regs4 22%bv = Z_to_bv 64 (G + 4)) by (kept K4 22 C22).
    (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (SHA, KHI - 256)]) (@nil kcell) (@nil kwin))
      10%nat [0x78590] (SCR [] []) constr:([(22%bv : reg, ZAdd (ZV 32) (ZL 4))]) [G] constr:([Some (SHA, KHI - 256)]) regs4 m3 rom 0x0aa500.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
    assert (K5 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs4 regs5) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    zx_reg ZR (10%bv : reg) as E10. zx_reg ZR (11%bv : reg) as E11. zx_reg ZR (1%bv : reg) as E1.
    rename ZM into M5. clear ZE ZR ZF.
    destruct (setsh_B rom true regs5 m3 (G + 4) 65 (Z_to_bv 64 0x0aa50c)) as (regs6 & M6 & K6).
    { rewrite E10; f_equal; lia. } { exact E11. } { exact E1. } { vm_compute. reflexivity. } { lia. } { lia. } { lia. }
    { eapply store_ok_of_def_in; [exact WG3|]. zwidth. lia. } { exact MC3. }
    cbn [negb] in M6.
    set (m4 := wbytes m3 _ _) in M6.
    assert (U45 : unch m3 m4 [(G + 4, G + 69)]).
    { unfold m4. eapply (unch_store_bs m3 (G + 4)); rewrite ?repeat_length; [lia | zwidth; lia | in_list | lia | lia]. }
    assert (G45 : mem_grows m3 m4) by (unfold m4; apply grows_store).
    eexists regs6, m4. split.
    { eapply msteps_trans; [exact M12|]. eapply msteps_trans; [exact M3|]. eapply msteps_trans; [exact M4|].
      eapply msteps_trans; [exact M5 | exact M6]. }
    split.
    { eapply bn_at_unch; [exact U45 | lia | cbn; lia | | exact Hbn4]. intros r Hr. inr Hr ltac:(slia). }
    split.
    { eapply keeps_trans; [exact K3|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|].
      eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity. }
    split.
    { eapply unch_trans; [unch_ns U02|]. eapply unch_trans; [unch_ns U34 | unch_ns U45]. }
    eapply mem_grows_trans; [exact G02|]. eapply mem_grows_trans; [exact G34 | exact G45]. }
  (* [comment removed for export] *)
  assert (CASES : 1 <= d < B \/ B <= d < B * B \/ B * B <= d < M64) by (unfold B; lia).
  destruct CASES as [Hv1 | [Hv2 | Hv3]].
  - rewrite chunks_1 in * by exact Hv1. unfold B in *.
    aa2_run 1 (2 ^ 28 - 1) regs2 m1 rom d.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L64'; exact I) ltac:(kwd WG1; kwd WF1; exact I) ltac:(idtac; zx_scs ltac:(flia)). zx_name regs3.
    zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (2%bv : reg) as C2. zx_reg ZR (1%bv : reg) as C1.
    assert (C22 : getr regs3 22%bv = Z_to_bv 64 (G + 4)) by (etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact B22]).
    assert (K3 : keeps AA2_KEEP regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
    clear ZE ZR ZF.
    eapply CONT; [exact ZM | rewrite C10; reflexivity | rewrite C11; f_equal; lia | rewrite C2; reflexivity | rewrite C1; reflexivity | exact C22 | |
                 | exact K3 | clear ZM CONT; unchx | growsx].
    + clear ZM CONT. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [d])) with 1.
      split; [cellx2|split; [cellx2|split; [|lia]]].
      apply arr32_store_other; zwidth; try lia.
      intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. replace (F + 32 + 4 + 4 * Z.of_nat 0) with (F + 36) by lia. cellx2.
    + clear ZM CONT. eapply (objshB_unch2 m1 _ [(g + 68, g + 69); (F + 32, F + 548)]); [unchx | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OB1].
  - rewrite chunks_2 in * by exact Hv2. unfold B in *.
    aa2_run (2 ^ 28) (2 ^ 56 - 1) regs2 m1 rom d.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L64'; exact I) ltac:(kwd WG1; kwd WF1; exact I) ltac:(idtac; zx_scs ltac:(flia)). zx_name regs3.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 1 <= d / 268435456 < 268435456) by lia.
    change (2 ^ 28) with 268435456 in *.
    zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (2%bv : reg) as C2. zx_reg ZR (1%bv : reg) as C1.
    assert (C22 : getr regs3 22%bv = Z_to_bv 64 (G + 4)) by (etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact B22]).
    assert (K3 : keeps AA2_KEEP regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
    clear ZE ZR ZF. change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456) as c2 eqn:E2. clear E1 E2.
    eapply CONT; [exact ZM | rewrite C10; reflexivity | rewrite C11; f_equal; lia | rewrite C2; reflexivity | rewrite C1; reflexivity | exact C22 | |
                 | exact K3 | clear ZM CONT; unchx | growsx].
    + clear ZM CONT. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2])) with 2.
      split; [cellx2|split; [cellx2|split; [|lia]]].
      apply arr32_store_other; zwidth; try lia.
      intros i Hi. cbn in Hi. destruct i as [|[|]]; [| |lia]; cbn [nth]; zwidth.
      * replace (F + 32 + 4 + 4 * 0) with (F + 36) by lia. cellx2.
      * replace (F + 32 + 4 + 4 * 1) with (F + 40) by lia. cellx2.
    + clear ZM CONT. eapply (objshB_unch2 m1 _ [(g + 68, g + 69); (F + 32, F + 548)]); [unchx | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OB1].
  - rewrite chunks_3 in * by exact Hv3. unfold B in *.
    aa2_run (2 ^ 56) (2 ^ 64 - 1) regs2 m1 rom d.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 L64'; exact I) ltac:(kwd WG1; kwd WF1; exact I) ltac:(idtac; zx_scs ltac:(flia)). zx_name regs3.
    assert (HB1 : 0 <= d mod 268435456 < 268435456) by lia. assert (HB2 : 0 <= d / 268435456 mod 268435456 < 268435456) by lia.
    assert (HB3 : 1 <= d / 268435456 / 268435456 < 256) by lia.
    change (2 ^ 28) with 268435456 in *.
    zx_reg ZR (10%bv : reg) as C10. zx_reg ZR (11%bv : reg) as C11. zx_reg ZR (2%bv : reg) as C2. zx_reg ZR (1%bv : reg) as C1.
    assert (C22 : getr regs3 22%bv = Z_to_bv 64 (G + 4)) by (etransitivity; [exact (reg_kept _ _ _ _ (22%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact B22]).
    assert (K3 : keeps AA2_KEEP regs regs3).
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K12|]; vm_compute; reflexivity | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]. }
    clear ZE ZR ZF. change (2 ^ 28) with 268435456 in *.
    remember (d mod 268435456) as c1 eqn:E1. remember (d / 268435456 mod 268435456) as c2 eqn:E2.
    remember (d / 268435456 / 268435456) as c3 eqn:E3. clear E1 E2 E3.
    eapply CONT; [exact ZM | rewrite C10; reflexivity | rewrite C11; f_equal; lia | rewrite C2; reflexivity | rewrite C1; reflexivity | exact C22 | |
                 | exact K3 | clear ZM CONT; unchx | growsx].
    + clear ZM CONT. unfold bn_at. cbn [cells BnModel.ex]. unfold zlen. change (Z.of_nat (length [c1; c2; c3])) with 3.
      split; [cellx2|split; [cellx2|split; [|lia]]].
      apply arr32_store_other; zwidth; try lia.
      intros i Hi. cbn in Hi. destruct i as [|[|[|]]]; [| | |lia]; cbn [nth]; zwidth.
      * replace (F + 32 + 4 + 4 * 0) with (F + 36) by lia. cellx2.
      * replace (F + 32 + 4 + 4 * 1) with (F + 40) by lia. cellx2.
      * replace (F + 32 + 4 + 4 * 2) with (F + 44) by lia. cellx2.
    + clear ZM CONT. eapply (objshB_unch2 m1 _ [(g + 68, g + 69); (F + 32, F + 548)]); [unchx | intros r Hr; inr Hr ltac:(slia) | lia | lia | exact OB1].
Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac inr H tac := cbn [In] in H; repeat (destruct H as [<-|H]; [tac|]); destruct H.
Ltac unch_ns U :=
  eapply unch_widen; [exact U|];
  let rg := fresh "rg" in let H := fresh "Hrg" in
  intros rg H; unfold NS; cbn [fst snd];
  inr H ltac:(first [ eexists; split; [left; reflexivity | cbn; lia]
                    | eexists; split; [right; left; reflexivity | cbn; lia]
                    | eexists; split; [right; right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 4 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 5 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 6 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 7 right; left; reflexivity | cbn; lia]
                    | unfold hide in *;
                      first [ eexists; split; [left; reflexivity | cbn; lia]
                    | eexists; split; [right; left; reflexivity | cbn; lia]
                    | eexists; split; [right; right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 3 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 4 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 5 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 6 right; left; reflexivity | cbn; lia]
                    | eexists; split; [do 7 right; left; reflexivity | cbn; lia] ] ]).
Ltac rngs := let rg := fresh "rg" in let H := fresh "Hrg" in
  intros rg H; unfold ambr, sl1r, sl2r, savr, highr; inr H ltac:(slia).
Ltac cellx2 :=
  lazymatch goal with
  | |- cellN _ (wbytes _ (Z_to_bv 64 _) (word_to_le_bytes _ _)) _ _ _ =>
      first
        [ assumption
        | apply bn_ctor_hi; [lia | zwidth; lia | lia]
        | apply cellN_store_same';
          [ cbn; lia | lia | zwidth; lia
          | rewrite ?u_Z2bv64; zwidth;
            first [ reflexivity | lia
                  | rewrite (Z.mod_small _ 18446744073709551616) by lia; first [apply Z.mod_small; lia | rewrite Z.mod_small by lia; lia | idtac]
                  | idtac ] ]
        | apply cellN_store_skip; [ flia | zwidth; flia | flia | zwidth; flia | zwidth; flia | cellx2 ]
        | idtac ]
  | |- cellN _ _ _ _ _ => first [assumption | eassumption | idtac]
  end.
Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].
