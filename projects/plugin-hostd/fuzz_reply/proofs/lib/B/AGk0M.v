(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGk0M.v (commit 30a1993588f, c5 + memnorm; file sha256 9a42c176f551) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/AGk0M.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10 (task MEMNORM, full Allocate): the memnorm-kept twin of AGk0E.sec_arms_e (the SECONDARY
   arms of the frame-generic Allocate walk, n >= 64513).
   rule 24: no function proved (kind: arm twins, frame corollaries).

   [sec_arms_em] is AGk0E.sec_arms_e with its leaf AGk0E.alloc_leaf0_e replaced by [alloc_leaf0_em]
   (alloc_leaf0_e plus `memnorm mem0 -> memnorm mem'`, MemnormT.memnorm_keep), from AGk0E's section hypotheses.
   AGioM.alloc_sec_em adds the model path ([alloc_leaf_intro_em]).

   Route (measurement secondary-frames.md (sha256 05a349cba232; internal record)): each arm ends in an arm-level raw frame relative to the
   entry memory mem0 whose zones are all mn_safe (not read-only, below TASK_SIZE).  No walk is re-run and no callee
   contract is needed beyond AGk0E's:
   - the grant arms: AGif4.sfin's sf_MEQF (AGif4.v:88-90; outside AGjm.WIN, AGif4.QRz on grow, AGif4.DXz), read in
     TAILg_em's leaf beside AGk0E's errno fact (MemnormSecLoc.memnorm_sfin_win);
   - the refusal arm: at_RETS's MEQ over AGjn.WINPN (AGjn.v:454), in [refuseS_em] (AGk0.refuseS, AGk0.v:355-390, with
     the keep; MemnormSecLoc.memnorm_winpn).  Unlike errno, the keep is not vacuous at PNull, so refuseS is copied.
   The leaf is fixed in the statements of TAILg, TAILgB, after_depot, grantS_ne, grantS_eq and sec_arms, so those are
   AGk0E's copied with the leaf replaced; the changed lines are marked (* memnorm *).  Every other lemma is AGk0's,
   cited over this file's copy of AGk0E's section variables.  AGk0, AGk0E and every existing statement are
   unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFhy AGhy AGhz AGi0 AGi4 AGi9 YB1h AGjm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h YG0j YG08 YF06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFia YFib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGid AGie AGif AGig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGjh AGji AGjj AGjn AGjo AGjk AGjl AGjp AGjq AGjr AGjt AGjz.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YF05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFi3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGjy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG AGif0reply AGif2 AGif4.
(* The image-free interface layer (C5 / image split) is used qualified: importing ImgBaseAGS would hide AGjm's
   geometry names behind its copies. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGif0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ImgBaseAGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0g YG0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGk0 ErrnoG ErrnoGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGk0E MemnormT MemnormSecLoc.
Local Unset Lia Cache. Local Unset Nia Cache.
(* copy of AGk0.v:41-47 *)
Local Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* copy of AGk0.v:47, 50-52 *)
Local Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Local Ltac step HR e :=
eapply SRr_bind; [exact e | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR].
Local Open Scope am_scope.

(* AGk0E.alloc_leaf0_e with the memnorm keep after errno (the order of MemnormT.alloc_leaf_em without its model-path
   clause, as alloc_leaf0_e is ErrnoG.alloc_leaf_e's). *)
Definition alloc_leaf0_em (B : asyms)
(ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop) (oomb inst : Z) (ly : alayout) (S : astate)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
alloc_post tfibsegs B ARX AOX inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
(fst r <> PNull -> ErrnoG.errno_kept B mem mem') /\
MemnormT.memnorm_keep tfibsegs mem mem' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(fst r = PNull -> val_mem tfibsegs (mrestrict (w_H W') mem') oomb 1 1).

(* Dropping the keep gives AGk0E's leaf. *)
Lemma alloc_leaf0_em_e : forall (B : asyms)
(ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop) (oomb inst : Z) (ly : alayout) (S : astate)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world tfibsegs) (c' : config),
alloc_leaf0_em B ARX AOX lpost oomb inst ly S W regs mem md n r W' c' ->
AGk0E.alloc_leaf0_e B ARX AOX lpost oomb inst ly S W regs mem md n r W' c'.
Proof.
intros B ARX AOX lpost oomb inst ly S W regs mem md n r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & _ & HR & HL & HO).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HR|].
split; [exact HL | exact HO].
Qed.

(* AGk0E.alloc_leaf_intro_e over alloc_leaf0_em: with the model path over the whole tree it is MemnormT.alloc_leaf_em. *)
Lemma alloc_leaf_intro_em : forall (B : asyms) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop) (oomb inst : Z) (ly : alayout) (S : astate)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z)
(r : sptr * astate) (W' : world tfibsegs) (c' : config),
alloc_leaf0_em B ARX AOX lpost oomb inst ly S W regs mem md n r W' c' ->
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & HK & HR & HL & HO) HPATH.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact HK|].
split; [exact HR|]. split; [exact HL|]. split; [exact HPATH | exact HO].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* copy of AGk0E.v:103-195: AGk0's section variables and hypotheses, in AGk0's order, and the errno add-on.         *)
Section f.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the call's state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis IFS : AGif4.AIfaceS B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
(* AGk0's widened bounds (AGk0.v Section f): the size NMAXW, the grant-existence bound NOBW and the room ROOMW. *)
Variables (NMAXW NOBW ROOMW : Z).
Hypothesis IFA : AGif4.ifs_apart_w ARX NMAXW.
Hypothesis IFG : AGif4.ifs_grant_w ARX NOBW.
Hypothesis IFR : AGif4.ifs_room_w ARX rpre ROOMW.
Hypothesis HNOB : NMAXW + 4 * 4096 <= NOBW.
Hypothesis HROOM : 2 * (NMAXW + 4 * 4096) + (NMAXW + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= ROOMW.
Hypothesis TS : TfibSyms B.
Variable inst : Z.
Variable ly : alayout.
Variable S : astate.
Variable W : world tfibsegs.
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let INSTv : Z := bv_unsigned (getr regs0 11).
Let T : Z := ly_T ly.
Let Qb : Z := ly_Q ly.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hcf : bv_unsigned (getr regs0 15) = 0 \/ bv_unsigned (getr regs0 15) = 1.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hinst : 0x9d000 <= INSTv /\ INSTv + 0xe60 <= 0x1288a0 /\ INSTv mod 8 = 0.
Hypothesis Nrange : 64513 <= n < SEC_NMAX.
Hypothesis HnW : n < NMAXW.
Hypothesis Hnmax : n < nmax.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypothesis SV : AGif2.sview B W ly INSTv mem0 idx res.
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Htr : U tr S.
Hypothesis Hlive : blocks_bytes S + n <= lmax.
Variable regsU : bvmap 5 word.
(* The seed at Allocate's entry, at every block base [mb] (AGjx.SEED_ok holds for any mb: the seed does not mention
   the block); the prefix uses it at mb := 0, the grant arms at the granted base. *)
Hypothesis SEED : forall mb, st_ok tfibsegs (AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) S_1
(restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
(* The errno add-on of AIfaceS (ErrnoGS.v): aes_post_grant is the errno fact at the grant leaf. *)
Hypothesis IFSE : ErrnoGS.AIfaceSE B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
(* AGk0's lemmas and definitions over this section's variables (their argument lists are AGk0's). *)
Local Abbreviation DPOST := (AGk0.DPOST dpost inst ly S W tr).
Local Abbreviation SRr_with_AI := AGk0.SRr_with_AI.
Local Abbreviation amreal_askV := AGk0.amreal_askV.
Local Abbreviation WFR := (AGk0.WFR ly W regs0 mem0 tr Hsp Htrlen Hso Hbp Hpres0).
Local Abbreviation aregs_of_RCS := (AGk0.aregs_of_RCS NMAXW ly S regs0 n tr res Htrlen Hinst Nrange HnW).
Local Abbreviation same_io_wvb := (AGk0.same_io_wvb md0).
Local Abbreviation S1 := (AGk0.S1 S).
Local Abbreviation QLEAF := (AGk0.QLEAF B ARX AOX lpost inst ly S W regs0 mem0 md0 n).
Local Abbreviation KSEC := (AGk0.KSEC stag S n tr).
Local Abbreviation sec_ask_eq := (AGk0.sec_ask_eq stag S n tr).
Local Abbreviation KDEP := (AGk0.KDEP stag n tr).
Local Abbreviation malloc_K_some := (AGk0.malloc_K_some stag n tr).
Local Abbreviation SH_hull := (AGk0.SH_hull NMAXW ly S regs0 n tr res Htrlen Hinst Nrange HnW).
Local Abbreviation pstable_and_ := AGk0.pstable_and_.
Local Abbreviation NR := (AGk0.NR ly S regs0 n tr res Htrlen Hinst Nrange).
Local Abbreviation NRb := (AGk0.NRb ly S regs0 n tr res Htrlen Hinst Nrange).
Local Abbreviation refuseS := (AGk0.refuseS B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS NMAXW TS inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hi11 Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange HnW Hnmax Hidx Hres Hidx_def Hres_def Hpres0 SV HARX HRP Htr Hlive regsU SEED).
(* AGk0.node_sec at mb := 0, over the leaf type of the model tree (its implicit RT given explicitly) *)
Local Abbreviation NODESEC_ := (@AGk0.node_sec fx rc B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IFS NMAXW NOBW ROOMW IFG IFR HNOB HROOM inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 Htrlen Hinst Nrange HnW HARX HRP 0 (sptr * astate)).
Local Abbreviation MSBW_g := (AGk0.MSBW_g NMAXW n Nrange HnW).
Local Abbreviation MS8_g := (AGk0.MS8_g NMAXW n Nrange HnW).
(* memnorm: the leaf *)
Local Abbreviation QLEAF_em := (alloc_leaf0_em B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk at a block base [mb] (copy of AGk0.v:260-311).                                                           *)
Section g.
Variable mb : Z.
Local Abbreviation MSv := (@AGjm.MSv n).
Local Abbreviation NDv := (@AGjm.NDv n).
Local Abbreviation N8D := (@AGjm.N8D n).
Local Abbreviation QSv := (@AGjm.QSv ly idx).
Local Abbreviation SMv := (@AGjm.SMv mb).
Local Abbreviation Uv := (@AGjm.Uv mb).
Local Abbreviation PBv := (@AGjm.PBv n mb).
Local Abbreviation UEv := (@AGjm.UEv n mb).
Local Abbreviation SHBv := (@AGjm.SHBv).
Local Abbreviation E0 := (@AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMAP := (@AGjm.EaMAP ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMS := (@AGjm.EaMS ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WINT := (@AGjm.WINT ly).
Local Abbreviation WINI := (@AGjm.WINI regs0 n).
Local Abbreviation WIN := (@AGjm.WIN ly regs0 n idx mb).
Local Abbreviation WINP := (@AGjm.WINP ly regs0 n).
Local Abbreviation DZONE := (@AGjm.DZONE ly).
Local Abbreviation at_S := (@AGjm.at_S _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@AGjm.at_N _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@AGjm.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@AGjm.pstable).
Local Abbreviation size_facts := (@AGjm.size_facts n Nrange).
Local Abbreviation sv_denot_SOff0 := (@AGjm.sv_denot_SOff0).
Local Abbreviation PBUF := (@AGjh.PBUF W regs0 tr).
Local Abbreviation PNULLX := (@AGjj.PNULLX W ly regs0 n tr idx res).
Local Abbreviation WINPN := (@AGjn.WINPN ly regs0 n).
Local Abbreviation WIN1T := (@AGjn.WIN1T ly regs0 n idx mb).
Local Abbreviation PBUFW := (@AGjn.PBUFW regs0 tr).
Local Abbreviation PSR := (@AGjo.PSR regs0 n tr mb).
Local Abbreviation rstable := (@AGjo.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@AGjo.rstable_true ly regs0 n mb).
Local Abbreviation QSP := (@AGjo.QSP ly idx).
Local Abbreviation brun := (@AGjo.brun).
Local Abbreviation SH0 := (@AGjk.SH0 n mb).
Local Abbreviation SH2 := (@AGjk.SH2 n mb).
Local Abbreviation QSPX := (@AGjl.QSPX ly idx).
Local Abbreviation QR := (@AGjp.QR ly res).
Local Abbreviation DX := (@AGjp.DX ly regs0).
Local Abbreviation PDX := (@AGjp.PDX ly mem0 DPOST).
Local Abbreviation SH4 := (@AGjp.SH4 n mb).
Local Abbreviation SH5 := (@AGjq.SH5 n mb).
Local Abbreviation SH6 := (@AGjq.SH6 n mb).
Local Abbreviation SH5o := (@AGjq.SH5o n mb).
Local Abbreviation SH6o := (@AGjq.SH6o n mb).
Local Abbreviation PT := (@AGjq.PT regs0 n tr mb).
Local Abbreviation ZQ := (@AGjt.ZQ ly idx res).
Local Abbreviation ZQF := (@AGjt.ZQF ly res).
Local Abbreviation RZ := (@AGjt.RZ ly idx res).
Local Abbreviation RZF := (@AGjt.RZF ly res).
Local Abbreviation FQ := (@AGjz.FQ ly regs0 n idx res mb).

(* memnorm: AGk0.refuseS (AGk0.v:355-390) with the keep.  The refusal leaf returns PNull, where the keep is not
   vacuous: it comes from at_RETS's MEQ (outside AGjn.WINPN) by MemnormSecLoc.memnorm_winpn.  AGk0.at_S_wvb and
   AGk0.segR_ are cited; their section arguments are found by unification and from the context. *)
Theorem refuseS_em : forall (mat : list word) c',
at_S W (with_vm_backing (m_vm_lazy md0) mat md0) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
amreal tfibsegs (KSEC 0) W c' QLEAF_em.
Proof.
intros mat c' HR. change (amreal tfibsegs (KSEC 0) W c' QLEAF_em) with (SRr tfibsegs W c' (QLEAF_em (PNull, S1))).
eapply AGk0.at_S_wvb in HR. eapply SRr_mono; [eapply AGk0.segR_; try eassumption; exact HR|].
intros W2 c2 _ (-> & regs' & mem' & mat2 & -> & R10 & RCS & MEQ & PRS & ((HB & VOOM) & (Vunw & Vres & Vnch & Vmtx & PRT & VISI))).
(* AGk0.INSTv_inst (AGk0.v:209-210) *)
assert (EI : bv_unsigned (getr regs0 11) = inst).
{ pose proof (AGif0n.if_inst _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem0 md0 HARX) as (I1 & I2 & _).
  rewrite Hi11. unfold YG0d.w64. apply unsigned_lit_small. lia. }
assert (SN : AGif4.snull W ly regs0 mem0 inst n (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) 0 regs' mem').
{ constructor.
  - exact R10.
  - exact RCS.
  - intros x N1 N2 N3. apply MEQ. intros [X|[X|X]]; [exact (N1 X) | apply N2; rewrite AGk0.ims_oom; lia | exact (N3 X)].
  - exact PRS.
  - exact PRT.
  - exact VISI.
  - exact VOOM.
  - exact Vunw.
  - rewrite <- Hres_def, <- EI. exact Vres.
  - rewrite <- Hidx_def, <- EI. exact Vnch.
  - rewrite <- EI. exact Vmtx. }
destruct (AGif4.ifs_post_null _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 n tr regs0 regs' mem' mat2 HARX HRP ltac:(lia) Hlive Htr WFR Hi11 SN)
as (HARX' & HLP & FR & FRraw).
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md0) mat2 md0).
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
  split; [exact (aregs_of_RCS regs' RCS)|].
  split; [apply YG0b.same_io_with_vm_backing|].
  split; [intros a Ra NO _ NS _; exact (FR a Ra NO NS)|].
  split; [intros x NO NO' NS _; exact (FRraw x NO NO' NS)|].
  intros a Ha. unfold spZ, AFSTACK_G in Ha. apply PRS. unfold AFSTACK. exact Ha. }
(* memnorm *)
split. { cbn [fst]. intros HNN. exfalso. exact (HNN eq_refl). }
split.
{ pose proof Hsp as (Hlo & _ & Hhi & _). pose proof Hinst as (I1 & I2 & _).
  exact (MemnormSecLoc.memnorm_winpn ly regs0 n mem0 mem' LY IMG Hlo Hhi I1 I2
    (@AGjm.BSLv_range ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx) MEQ). }
split. { rewrite R10. cbn [fst sptr_addr sptr_exp aeval]. reflexivity. }
split; [exact HLP|].
intros _. exact VOOM.
Unshelve. all: try exact dpost; try exact S; try exact mem0; try exact md0; try exact 0%Z.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The grant arms, at the granted base [mb] (copy of AGk0.v:502-541).                                                *)
Section h.
Hypothesis Hmap : mb mod 4096 = 0 /\ AGjm.mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Variables (W3 : world tfibsegs) (mat : list word) (ms : machine_state) (E' : env) (mb0 : Z).
Let mdN : Model := with_vm_backing (m_vm_lazy md0) mat md0.
Let md2 : Model := mmap_model (w64 mb) (w64 MSv) mdN.
Let ccont : config := mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md2.
Hypothesis GOK : grant_ok_na_pin mdN (w64 mb) MSv = true.
Hypothesis LE3 : wle W W3.
Hypothesis SUB3 : hsub (w_H W3) (w_H W).
Hypothesis MON3 : forall x : word, w_H W x = false -> w_H W3 x = false.
Hypothesis A3 : w_A W3 = (AGif4.SHLO mb, AGif4.SHHI mb MSv) :: (mb, mb + MSv) :: w_A W.
Hypothesis VISM3 : forall x : word, mb <= bv_unsigned x < mb + MSv -> w_H W3 x = false.
Hypothesis VISH3 : forall x : word, AGif4.SHLO mb <= bv_unsigned x < AGif4.SHHI mb MSv -> w_H W3 x = false.
Hypothesis OUT3 : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (AGif4.SHLO mb <= bv_unsigned x < AGif4.SHHI mb MSv) -> w_H W3 x = w_H W x.
Hypothesis MW2 : amwf md2.
Hypothesis IO2 : same_io md0 md2.
Hypothesis EG2 : eager_used md2 <= eager_used mdN + MSv.
Hypothesis VM2 : vm_maps (m_vmmaps md2) = (w64 mb, w64 MSv) :: vm_maps (m_vmmaps mdN) /\ vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps mdN) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps mdN) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps mdN) /\
vm_init_sp (m_vmmaps md2) = vm_init_sp (m_vmmaps mdN).
Hypothesis HE' : env_agree sHAV (AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb0) E'.
Hypothesis HS : st_ok_ecall tfibsegs E' S_N (restrict (w_H W) ms).
Hypothesis MEQ : forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x.
Hypothesis PRS : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Hypothesis HB : PBUF (ms_mem ms).
Local Abbreviation map_facts := (@AGjm.map_facts _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation map_zoneN := (@AGjm.map_zoneN _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation high_facts := (@AGjm.high_facts _ ly regs0 tr idx res LY IMG Htrlen Hinst Hidx Hres).
Local Abbreviation stack_ivs := (@AGjm.stack_ivs _ ly regs0 tr idx res LY Hsp Htrlen Hbp Hinst Hidx Hres).
Local Abbreviation blocks_facts := (@AGjm.blocks_facts _ ly LY IMG).
Local Abbreviation HCX := (@AGjm.HCX _ ly LY).
Local Abbreviation BSLv_range := (@AGjm.BSLv_range ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx).
Local Abbreviation DZONE_disj := (@AGjm.DZONE_disj _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_facts := (@AGjm.at_S_facts _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_ret := (@AGjm.at_S_ret _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres).
(* AGk0's lemmas at this block base, over this section's variables (their argument lists are AGk0's). *)
Local Abbreviation mb_range := (AGk0.mb_range ly regs0 n tr idx res Htrlen Hinst Nrange Hidx Hres mb Hmap).
Local Abbreviation SHZ := (AGk0.SHZ ARX NMAXW IFA inst ly S W regs0 mem0 md0 n tr idx res LY IMG Hsp Htrlen Hinst Nrange HnW Hidx Hres HARX mb Hmap W3 mat ms GOK VISH3 MEQ).
Local Abbreviation VISM := (AGk0.VISM ly regs0 n tr idx res Htrlen Hinst Nrange Hidx Hres mb Hmap W3 VISM3).
Local Abbreviation QSP3 := (AGk0.QSP3 B ly W regs0 mem0 n tr idx res LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres SV mb Hmap Hmap_apart W3 ms MON3 MEQ).
Local Abbreviation grant_cont_ := (AGk0.grant_cont_ ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres regsU SEED mb Hmap Hmap_apart ms E' mb0 HE' HS MEQ PRS HB).
Local Abbreviation segG1_ := (AGk0.segG1_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segNE_ := (AGk0.segNE_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segEQa_ := (AGk0.segEQa_ ly W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segJ_ := (AGk0.segJ_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segT1_ := (AGk0.segT1_ ly W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hsp Htrlen Hbp Hinst Nrange Hidx Hres regsU SEED mb Hmap Hmap_apart).
Local Abbreviation at_S_depot_ := (AGk0.at_S_depot_ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS NMAXW IFA inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hi11 Hgp Hcf Hsp Htrlen Hso Hbp Hinst Nrange HnW Hidx Hres Hidx_def Hres_def HARX Htr regsU SEED mb Hmap Hmap_apart mat GOK VM2).
Local Abbreviation segT2_ := (AGk0.segT2_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segU1_ := (AGk0.segU1_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segUe_ := (AGk0.segUe_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segUo_ := (AGk0.segUo_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segUe0_ := (AGk0.segUe0_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hsp Htrlen Hbp Hinst Nrange Hidx Hres regsU SEED mb Hmap Hmap_apart).
Local Abbreviation segUo0_ := (AGk0.segUo0_ dpost inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation QR_facts_ := (AGk0.QR_facts_ NMAXW ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Htrlen Hinst Hidx Hres Hidx_def regsU SEED mb mb0).
Local Abbreviation ZQ_rstable_ := (AGk0.ZQ_rstable_ NMAXW ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hidx_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation ZQ_stableT_ := (AGk0.ZQ_stableT_ NMAXW ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hidx_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation ZQ_stableD_ := (AGk0.ZQ_stableD_ NMAXW ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hinst Hidx Hres Hidx_def regsU SEED mb mb0).
Local Abbreviation QSP_rstable_ := (AGk0.QSP_rstable_ ly W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hinst Nrange Hidx Hres regsU SEED mb Hmap Hmap_apart).
Local Abbreviation rstable_and_ := (AGk0.rstable_and_ ly W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 regsU SEED mb).
Local Abbreviation segV_ := (AGk0.segV_ dpost NMAXW inst ly S W regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart).
Local Abbreviation finpost := (AGk0.finpost dpost inst ly S W regs0 mem0 n tr idx res mb).
Local Abbreviation finEG := (AGk0.finEG B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF NMAXW inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hi11 Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def HARX mb Hmap).
Local Abbreviation finOG := (AGk0.finOG B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF NMAXW inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hi11 Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def HARX mb Hmap).
Local Abbreviation finEG0 := (AGk0.finEG0 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF NMAXW inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hi11 Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def HARX mb Hmap).
Local Abbreviation finOG0 := (AGk0.finOG0 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF NMAXW inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hn Hi11 Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def HARX mb Hmap).
(* AGk0.nodeV_ over the leaf type of the model tree (its implicit RT given explicitly) *)
Local Abbreviation NODEV_ := (@AGk0.nodeV_ fx rc dpost NMAXW inst ly S W regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hidx_def Hres_def regsU SEED mb Hmap Hmap_apart (sptr * astate)).

(* The model's tail after the depot answer, and the leaf through ifs_post_grant and aes_post_grant. *)
(* copy of AGk0E.v:329-405, the leaf QLEAF_em (memnorm) *)
Lemma TAILg_em : N8D / 8 < 18446744073709551615 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
(forall matF, AGif4.skern grow W Wz md0 (with_vm_backing (m_vm_lazy mdz) matF mdz) ly mb MSv QSv) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s4 = st_depot (depot_after z tr S) -> st_chunks s4 = st_chunks S -> st_secs s4 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s4 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s4 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s4 = st_regions S ->
st_nev s4 = st_nev S + 1 -> st_cache_inited s4 = st_cache_inited S -> st_cache s4 = st_cache S -> st_qthread s4 = st_qthread S ->
st_qglobal s4 = st_qglobal S -> st_fs s4 = st_fs S -> st_internal_inited s4 = st_internal_inited S ->
amreal tfibsegs ((YG00.ret tt ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF_em.
Proof.
intros Hsmall grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub HSK HR D4 C4 SE4 A4 R4 RG4 N4 CI4 CA4 QT4 QG4 FS4 II4.
pose proof (AGjy.sizes_model ly regs0 n tr res Htrlen Hinst Nrange S) as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal].
assert (LEAF : forall W' c', finpost Wz mdz grow z W' c' ->
QLEAF_em (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated), set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4) W' c').
{ intros W' c' (-> & regs' & mem' & matF & -> & HF).
pose proof HF as [Fdep MEQF FPRS _ _ _ _ _ FR10 FRCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
destruct Fdep as (memD & DP & _).
pose proof (AGif0n.if_dpost_aok _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W tr z memD DP) as AOK.
pose proof (AGif4.ifs_fresh _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 HARX) as FRESH.
assert (EQS : set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4 = AGif4.SFSz S n tr z grow).
{ pose proof (YFib.upd_chunk_fresh (st_chunks S) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) FRESH) as UF.
clear HR HF HSK FPRS FR10 FRCS. destruct s4.
cbn in D4, C4, SE4, A4, R4, RG4, N4, CI4, CA4, QT4, QG4, FS4, II4 |- *. subst.
unfold AGif4.SFSz, ImgBaseAGS.sfinal, ImgBaseAGS.depF, ImgBaseAGS.resF, ImgBaseAGS.KS, ImgBaseAGS.rS. cbn. cbn in UF. rewrite UF.
rewrite MS, ND. unfold depot_after. destruct grow; destruct (z =? 0); reflexivity. }
assert (Hgrow' : grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) by (rewrite <- Hidx_def, <- Hres_def; exact Hgrow).
pose proof (HSK matF) as SK. pose proof SK as [Kmbr Kmd Kwle Kio Kmwf Kmon Kvismap Kvissh Kvisq Kab Kinc Kamap Kahull Kout].
rewrite Hidx_def in SK.
pose proof HF as HF'. rewrite Hidx_def, Hres_def in HF'.
destruct (AGif4.ifs_post_grant _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 n tr regs0 mb grow z Wz (with_vm_backing (m_vm_lazy mdz) matF mdz) regs' mem'
HARX HRP ltac:(lia) Hlive Htr WFR Hi11 Hgrow' SK HF' AOK) as (HARX' & HLP & HLE & HADDR & HFR & HFRraw).
(* + errno: the add-on at the same point, with the same arguments *)
pose proof (ErrnoGS.aes_post_grant _ _ _ _ _ _ _ _ _ _ _ _ IFSE inst ly S W mem0 md0 n tr regs0 mb grow z Wz (with_vm_backing (m_vm_lazy mdz) matF mdz) regs' mem'
HARX HRP ltac:(lia) Hlive Htr WFR Hi11 Hgrow' SK HF' AOK) as HERR.
assert (KU : ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) = ck_user (ImgBaseAGS.KS S n)) by reflexivity.
assert (KNN : ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) <> PNull) by (unfold ck_user, padd; cbn; discriminate).
rewrite EQS.
exists (AGif4.lyFz ly S mb), regs', mem', (with_vm_backing (m_vm_lazy mdz) matF mdz).
split. { unfold cfg_at, raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact HARX'|]. split; [exact HLE|]. split; [exact Kwle|].
  split; [exact (aregs_of_RCS regs' FRCS)|].
  split; [exact Kio|].
  split.
  { intros a Ra NO NO' NS NE. apply (HFR a Ra NO NO' NS). intros Hu. apply NE. cbn [fst]. split; [exact KNN|]. rewrite KU, HADDR. exact Hu. }
  split.
  { intros x NO NO' NS NE. apply (HFRraw x NO NO' NS). intros Hu. apply NE. cbn [fst]. split; [exact KNN|]. rewrite KU, HADDR. exact Hu. }
  intros a Ha. unfold spZ, AFSTACK_G in Ha. apply FPRS. unfold AFSTACK. exact Ha. }
split. { intros _. exact HERR. }
(* memnorm: the grant post's raw frame (AGif4.sf_MEQF) over safe zones (MemnormSecLoc.memnorm_sfin_win) *)
split.
{ pose proof Hsp as (Hlo & _ & Hhi & _). pose proof Hinst as (I1 & I2 & _).
  exact (MemnormSecLoc.memnorm_sfin_win ly regs0 n idx res mb grow mem0 mem' LY IMG Hlo Hhi I1 I2 BSLv_range Hidx
    ltac:(lia) (Z.lt_le_incl _ _ (proj1 MSBW_g)) (AGjm.mzone_zone3 _ _ (proj2 Hmap)) MEQF). }
split. { cbn [fst]. rewrite FR10, KU, HADDR. reflexivity. }
split; [exact HLP|].
cbn [fst]. intros Hp. exfalso. exact (KNN Hp). }
step HR (segT2_ Wz mdz RX RXs RXt Xd z HXW _ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segU1_ Wz mdz RX RXs RXt Xd z HXW Hsmall _ _ HR). pose proof (proj1 HR) as EW. subst W0.
pose proof Hcf as [C0|C1].
- destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
  + step HR (segUe0_ Wz mdz RX RXs RXt Xd z HXW Hsmall C0 H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
    eapply SRr_mono; [exact (finEG0 Wz mdz Xd RX grow z Hgrow HXsub HRXQ C0 H8 _ _ HR)|].
    intros W' c' _ HP. exact (LEAF W' c' HP).
  + step HR (segUo0_ Wz mdz RX RXs RXt Xd z HXW Hsmall C0 H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
    eapply SRr_mono; [exact (finOG0 Wz mdz Xd RX grow z Hgrow HXsub HRXQ C0 H8 _ _ HR)|].
    intros W' c' _ HP. exact (LEAF W' c' HP).
- assert (CNE : bv_unsigned (getr regs0 15) <> 0) by lia.
  destruct (Z.eq_dec (n mod 8) 0) as [H8|H8].
  + step HR (segUe_ Wz mdz RX RXs RXt Xd z HXW Hsmall CNE H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
    eapply SRr_mono; [exact (finEG Wz mdz Xd RX grow z Hgrow HXsub HRXQ H8 _ _ HR)|].
    intros W' c' _ HP. exact (LEAF W' c' HP).
  + step HR (segUo_ Wz mdz RX RXs RXt Xd z HXW Hsmall CNE H8 _ _ HR). pose proof (proj1 HR) as EW. subst W0.
    eapply SRr_mono; [exact (finOG Wz mdz Xd RX grow z Hgrow HXsub HRXQ H8 _ _ HR)|].
    intros W' c' _ HP. exact (LEAF W' c' HP).
Qed.
(* copy of AGk0E.v:406-417, the leaf QLEAF_em (memnorm) *)
Lemma TAILgB_em : 18446744073709551615 <= N8D / 8 -> forall (Wz : world tfibsegs) (c4 : config) (s4 : astate),
amreal tfibsegs (((z' <- askz (KShadowRemap (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated))
(8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8))) ;;
(if aGranted z' then YG00.ret tt else spin stag)) ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF_em.
Proof.
intros Hbig. exfalso. pose proof Nrange as NRs. clear - Hbig NRs. unfold AGjm.N8D in Hbig. unfold SEC_NMAX in NRs.
rewrite Z.div_mul in Hbig by (clear; lia).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 27) ltac:(clear; lia) ltac:(clear - NRs; lia)) as HH. clear NRs. lia.
Qed.
(* copy of AGk0E.v:418-453, the leaf QLEAF_em (memnorm) *)
Lemma after_depot_em : forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s3,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
(forall matF, AGif4.skern grow W Wz md0 (with_vm_backing (m_vm_lazy mdz) matF mdz) ly mb MSv QSv) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s3 = st_depot S -> st_chunks s3 = st_chunks S -> st_secs s3 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s3 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s3 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s3 = st_regions S ->
st_nev s3 = st_nev S + 1 -> st_cache_inited s3 = st_cache_inited S -> st_cache s3 = st_cache S -> st_qthread s3 = st_qthread S ->
st_qglobal s3 = st_qglobal S -> st_fs s3 = st_fs S -> st_internal_inited s3 = st_internal_inited S ->
amreal tfibsegs (KDEP s3 (PSec (length (st_secs S1)) kPage) z) Wz c4 QLEAF_em.
Proof.
intros grow Wz mdz RX Xd z c4 s3 Hgrow RXs RXt HRXQ HXW HXsub HSK HR D3 C3 SE3 A3' R3 RG3 N3 CI3 CA3 QT3 QG3 FS3 II3.
unfold AGk0.KDEP. destruct (Z_lt_le_dec (N8D / 8) 18446744073709551615) as [Hsm|Hbg].
- pose proof (fun s4 => TAILg_em Hsm grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub HSK HR) as TAIL.
rewrite (NR Hsm).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). reflexivity.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). reflexivity.
- pose proof (fun s4 => TAILgB_em Hbg Wz c4 s4) as TAIL.
rewrite (NRb Hbg).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL.
Qed.

(* copy of AGk0E.v:455-506, the leaf QLEAF_em (memnorm) *)
(* The arm where the pointer array still has a reserved slot. *)
Theorem grantS_ne_em : idx <> res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF_em.
Proof.
intros NE. pose proof Hidx as HI. pose proof Hres as [HRS HRA].
pose proof (grant_cont_ W3 md2 (QSPX W3 (fun _ => True)) SUB3 VISM SHZ (conj (QSP3 NE) I)) as HR.
unfold AGk0.KSEC. change (1 =? 0) with false. cbn iota. unfold AGk0.sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold AGk0.S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with false by (symmetry; apply Z.eqb_neq; unfold AGk0.S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact NE).
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
rewrite malloc_K_some.
pose proof (rstable_and_ (QSP W3) (fun _ => True) (QSP_rstable_ W3) rstable_true) as RST.
assert (RXs : rstable (fun _ : word -> option byte => True)) by exact rstable_true.
assert (RXt : pstable WIN1T (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
assert (RXd : pstable DX (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
assert (HXW : forall a, WIN a -> WIN a) by (clear; intros a H; exact H).
assert (HXQ : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
step HR (segG1_ W3 md2 _ RST ccont HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segNE_ W3 md2 (fun _ => True) RXs RXt NE _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ_ W3 md2 (fun _ => True) RXs RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1_ W3 md2 (fun _ => True) RXs RXt WIN HXW _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot_ W3 md2 (fun _ => True) RXs RXt RXd MON3 WIN HXQ HXW _ HR) | clear HR; intros W4 c4 _ [z HR]].
pose proof (proj1 HR) as EW. subst W4.
pose proof HR as HRc. destruct HRc as (_ & ms4 & mat4 & E4 & Ec4 & HE4 & HS4 & MEQ4 & PRS4 & [HPS4 [HPD4 _]]).
destruct HPD4 as (memD & DP & PRD & EQD).
pose proof (AGif0n.if_dpost_aok _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W tr z memD DP) as AOKz.
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : false = true <-> idx = res) by (split; [intros E; discriminate E | intros E; exfalso; exact (NE E)]).
assert (HXsub : forall a, (WIN a \/ DX a) -> WIN a \/ (false = true /\ QR a) \/ DX a) by (clear; intros a [Ha|Ha]; tauto).
assert (HRXQ : false = true -> forall m : word -> option byte, True -> ZQ W3 m) by (intros E; discriminate E).
assert (HXW' : forall a, WIN a -> WIN a \/ DX a) by (clear; intros a H; left; exact H).
assert (SK3 : forall matF, AGif4.skern false W W3 md0 (with_vm_backing (m_vm_lazy md2) matF md2) ly mb MSv QSv).
{ intros matF. pose proof (SH_hull mb) as (H1 & H2 & H3 & _). constructor.
  - exact mb_range.
  - exists mat, [], matF. split; [reflexivity|]. split; [exact GOK|]. split; [exact MW2 | intros E; discriminate E].
  - exact LE3.
  - exact (same_io_wvb md2 matF IO2).
  - exact (amwf_same md2 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2).
  - exact MON3.
  - exact VISM3.
  - exact VISH3.
  - intros E; discriminate E.
  - cbn [ImgBase.im_segs AImg_reply]. rewrite A3. cbn [A_bytes fst snd]. zlia.
  - intros i Hi. cbn [ImgBase.im_segs AImg_reply]. rewrite A3. cbn. right; right. exact Hi.
  - cbn [ImgBase.im_segs AImg_reply]. rewrite A3. cbn. right; left. reflexivity.
  - cbn [ImgBase.im_segs AImg_reply]. rewrite A3. cbn. left. reflexivity.
  - intros x N1 N2 _. exact (OUT3 x N1 N2). }
apply (after_depot_em false W3 md2 (fun _ => True) (fun a => WIN a \/ DX a) z c4 _ Hgrow RXs RXt HRXQ HXW' HXsub SK3 HR);
unfold AGk0.S1; cbn; reflexivity.
Qed.

(* copy of AGk0E.v:508-593, the leaf QLEAF_em (memnorm) *)
(* The arm where the pointer array is full: the kernel also commits its next page (AGjt.nodeV). *)
Theorem grantS_eq_em : idx = res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF_em.
Proof.
intros EQ. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof (QR_facts_ EQ) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof (AGif4.ifs_ledger _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 HARX) as (LR & LSEG & LQ & LTOP).
pose proof (IFR inst ly S W mem0 md0 n HARX HRP) as ROOM. cbn [ImgBase.im_segs AImg_reply] in ROOM.
pose proof (grant_cont_ W3 md2 (fun _ => True) SUB3 VISM SHZ I) as HR.
unfold AGk0.KSEC. change (1 =? 0) with false. cbn iota. unfold AGk0.sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold AGk0.S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with true by (symmetry; apply Z.eqb_eq; unfold AGk0.S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact EQ).
rewrite !bind_assoc_eq. unfold YG00.bind at 1. unfold askz. cbn [ibind].
replace (8 * Z.of_nat (length (st_sec_arr S1))) with (8 * idx) by (unfold AGk0.S1; cbn; rewrite <- Hidx_def; reflexivity).
lazymatch goal with |- amreal _ (IAsk _ ?s ?Kc) _ _ _ => set (KV := Kc); set (sV := s) end.
apply amreal_askV; [exact I|].
assert (RXs : rstable (fun _ : word -> option byte => True)) by exact rstable_true.
assert (RXt0 : pstable WIN1T (fun _ : word -> option byte => True)) by (clear; intros m m' _ _; exact I).
step HR (segG1_ W3 md2 _ RXs ccont HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (segEQa_ W3 md2 (fun _ => True) RXs RXt0 EQ _ HR))|].
clear HR. intros W4 c4 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W4.
pose proof HN as HNc. destruct HNc as (_ & msV & matV & EV & EcV & _).
set (mdV := with_vm_backing (m_vm_lazy md2) matV md2) in *.
assert (EcM : cfg_model c4 = mdV) by (rewrite EcV; reflexivity).
assert (MWV : amwf mdV) by (exact (amwf_same md2 mdV (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2)).
pose proof VM2 as (VMa & VMr & VMl & VMb & VMi).
apply (NODEV_ W3 md2 sV KV QLEAF_em (fun _ => True) c4 EQ HN HAI).
- clear; intros m m' _ _; exact I.
- rewrite EcM. exact MWV.
- rewrite EcM. unfold mdV. rewrite m_vmmaps_wvb, VMr. unfold mdN. rewrite m_vmmaps_wvb. exact LR.
- exact LSEG.
- rewrite EcM. unfold mdV. rewrite m_vmmaps_wvb, VMa. right. unfold mdN. rewrite m_vmmaps_wvb. exact LQ.
- rewrite EcM. unfold mdV. rewrite eager_used_wvb, m_vmmaps_wvb, VMl. unfold mdN in EG2 |- *. rewrite m_vmmaps_wvb. rewrite eager_used_wvb in EG2.
rewrite A3. cbn [A_bytes fst snd].
pose proof MSBW_g as MSBW. pose proof MS8_g as MS8.
clear - ROOM EG2 H3 Z9 MSBW MS8 HROOM. zlia.
- rewrite EcM. unfold mdV. rewrite m_vmmaps_wvb. unfold alloc_top. rewrite VMi. unfold mdN. rewrite m_vmmaps_wvb. exact LTOP.
- intros z Hz. exact Hz.
- intros W5 c5. rewrite EcM. intros md5 LE5 SUB5 MON5 A5 VIS5 OUT5 AI5 MW5 IO5 EG5 VM5 HR5.
subst KV sV. cbv beta. change (aGranted 1) with true. cbn iota.
rewrite ?bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite ?bind_assoc_eq. eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
rewrite malloc_K_some.
assert (RS5 : rstable (RZ W5 (fun _ => True))) by (exact (rstable_and_ _ _ RXs (ZQ_rstable_ W5))).
assert (RT5 : pstable WIN1T (RZ W5 (fun _ => True))) by (apply pstable_and_; [clear; intros m m' _ _; exact I | exact (ZQ_stableT_ W5)]).
assert (RD5 : pstable DX (RZ W5 (fun _ => True))) by (apply pstable_and_; [clear; intros m m' _ _; exact I | exact (ZQ_stableD_ W5)]).
assert (HXW5 : forall a, WIN a -> WIN a \/ QR a) by (clear; intros a H; left; exact H).
assert (HXQ5 : forall a, (WIN a \/ QR a) -> WIN a \/ QR a) by (clear; intros a H; exact H).
assert (MON35 : forall x : word, w_H W x = false -> w_H W5 x = false) by (intros x Hx; exact (MON5 x (MON3 x Hx))).
assert (LE35 : wle W W5) by (exact (wle_trans _ _ _ _ LE3 LE5)).
pose proof HR5 as HR. clear HR5.
step HR (segV_ W5 md5 (fun _ => True) RXs EQ _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segJ_ W5 md5 (RZ W5 (fun _ => True)) RS5 RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
step HR (segT1_ W5 md5 (RZ W5 (fun _ => True)) RS5 RT5 (fun a => WIN a \/ QR a) HXW5 _ HR). pose proof (proj1 HR) as EW. subst W0.
eapply SRr_bind; [exact (at_S_depot_ W5 md5 (RZ W5 (fun _ => True)) RS5 RT5 RD5 MON35 (fun a => WIN a \/ QR a) HXQ5 HXW5 _ HR) | clear HR; intros W6 c6 _ [z HR]].
pose proof (proj1 HR) as EW. subst W6.
pose proof HR as HRc. destruct HRc as (_ & ms6 & mat6 & E6 & Ec6 & HE6 & HS6 & MEQ6 & PRS6 & [HPS6 [HPD6 _]]).
destruct HPD6 as (memD & DP & PRD & EQD).
pose proof (AGif0n.if_dpost_aok _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W tr z memD DP) as AOKz.
apply SRr_ret. exists z. split; [exact AOKz|].
assert (Hgrow : true = true <-> idx = res) by (split; [intros _; exact EQ | intros _; reflexivity]).
assert (HXsub : forall a, ((WIN a \/ QR a) \/ DX a) -> WIN a \/ (true = true /\ QR a) \/ DX a) by (clear; intros a [[Ha|Ha]|Ha]; tauto).
assert (HRXQ : true = true -> forall m : word -> option byte, RZ W5 (fun _ => True) m -> ZQ W5 m) by (intros _ m [_ Hm]; exact Hm).
assert (HXW' : forall a, WIN a -> (WIN a \/ QR a) \/ DX a) by (clear; intros a H; left; left; exact H).
assert (SK5 : forall matF, AGif4.skern true W W5 md0 (with_vm_backing (m_vm_lazy md5) matF md5) ly mb MSv QSv).
{ intros matF. constructor.
  - exact mb_range.
  - exists mat, matV, matF. split; [reflexivity|]. split; [exact GOK|]. split; [exact MW2|].
    intros _. rewrite eager_used_wvb. unfold mdV in EG5. rewrite eager_used_wvb in EG5. exact EG5.
  - exact LE35.
  - exact (same_io_wvb md5 matF IO5).
  - exact (amwf_same md5 _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW5).
  - exact MON35.
  - intros x Hx. exact (MON5 x (VISM3 x Hx)).
  - intros x Hx. exact (MON5 x (VISH3 x Hx)).
  - intros _ x Hx. exact (VIS5 x Hx).
  - cbn [ImgBase.im_segs AImg_reply]. rewrite A5, A3. cbn [A_bytes fst snd]. zlia.
  - intros i Hi. cbn [ImgBase.im_segs AImg_reply]. rewrite A5, A3. cbn. right; right; right. exact Hi.
  - cbn [ImgBase.im_segs AImg_reply]. rewrite A5, A3. cbn. right; right; left. reflexivity.
  - cbn [ImgBase.im_segs AImg_reply]. rewrite A5, A3. cbn. right; left. reflexivity.
  - intros x N1 N2 N3. cbn [ImgBase.im_segs AImg_reply]. rewrite (OUT5 x (fun H => N3 (conj eq_refl H))). exact (OUT3 x N1 N2). }
apply (after_depot_em true W5 md5 (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX a) z c6 _ Hgrow RS5 RT5 HRXQ HXW' HXsub SK5 HR);
unfold AGk0.S1; cbn; try reflexivity.
- rewrite EcM. exact (same_io_wvb md2 matV IO2).
Qed.
End h.
End g.

(* copy of AGk0E.v:597-646, the leaf alloc_leaf0_em (memnorm) *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The secondary arms from Allocate's entry: the prefix to the mmap ecall at mb := 0, the node, and the arms at the
   granted base.  The leaf is alloc_leaf0_em over regs0; AGioM adds the model path. *)
Lemma sec_arms_w_em :
amreal tfibsegs ((ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t stag n tr ob) (set_nev (st_nev S + 1) S)) W
(cfg_at tfibsegs A_Allocate regsU mem0 md0)
(alloc_leaf0_em B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n).
Proof using B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS NMAXW NOBW ROOMW IFA IFG IFR HNOB HROOM TS inst ly S W regs0 mem0 md0 n tr
idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp Hgp Hra Hra4096 Hcf Hsp Htrlen Hso Hbp
Hinst Nrange HnW Hnmax Hidx Hres Hidx_def Hres_def Hpres0 PBUF0 SV HARX HRP Htr Hlive regsU SEED IFSE.
change (set_nev (st_nev S + 1) S) with S1.
rewrite sec_ask_eq. cbn [amreal].
pose proof (@AGjh.seg0 _ W ly regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 Hpres0 (m_vm_materialized md0) regsU (SEED 0) PBUF0) as PFX.
unfold cfg_at. replace md0 with (with_vm_backing (m_vm_lazy md0) (m_vm_materialized md0) md0) at 1 by (apply with_vm_backing_id).
eapply SRr_bind; [exact PFX|]. clear PFX. intros W1 c1 _ HR1. pose proof (proj1 HR1) as EW. subst W1.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (@AGji.seg1 _ _ W ly regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 LY IMG Hn Hsp Htrlen Hbp Hinst Nrange Hidx Hres _ _ HR1))|].
clear HR1 c1. intros W1 c1 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W1.
pose proof HN as HNc. destruct HNc as (_ & ms1 & mat1 & E1 & Ec1 & _).
assert (EcM : cfg_model c1 = with_vm_backing (m_vm_lazy md0) mat1 md0) by (rewrite Ec1; reflexivity).
apply (NODESEC_ S1 KSEC QLEAF_em c1 HN HAI).
- intros z Hz. exact Hz.
- (* memnorm: the refusal arm returns PNull: refuseS_em (AGk0.refuseS with the keep) *)
  intros c' HRf. rewrite EcM in HRf. exact (refuseS_em 0 mat1 c' HRf).
- intros a W3 ms E'. cbv zeta. rewrite EcM.
intros GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 AI2 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB.
set (A := bv_unsigned a) in *.
assert (EA : a = w64 A) by (unfold w64, A; symmetry; apply Z_to_bv_bv_unsigned).
rewrite EA in GOK, AI2, MW2, IO2, EG2, VM2. rewrite EA.
pose proof (AGjm.size_facts n Nrange) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _).
pose proof MSBW_g as MSBW.
pose proof (YFia.grant_parts _ (w64 A) _ GOK) as (GP1 & _).
destruct (IFA inst ly S W mem0 md0 mat1 (AGjm.MSv n) (w64 A) HARX MSBW Z9 GOK) as (GH & GA & _).
assert (UA : bv_unsigned (w64 A) = A) by (rewrite <- EA; reflexivity). rewrite UA in GP1, GH, GA.
assert (HmapA : A mod 4096 = 0 /\ AGjm.mzone A (AGjm.MSv n)) by (split; [exact GP1 | exact GH]).
assert (GAx : forall e, In e (static_extents ly ++ vis0_zones ly) -> zdisjoint (A, AGjm.MSv n) e).
{ intros e He. apply (proj1 (Forall_forall _ _) GA). rewrite app_assoc. apply in_app_iff. left. exact He. }
assert (HapartA : zdisjoint (A, AGjm.MSv n) (ly_T ly, kThreadObjSize) /\ zdisjoint (A, AGjm.MSv n) (ly_C ly, kCtxMapSize) /\
zdisjoint (A, AGjm.MSv n) (ly_prim ly, kPrimResvSize) /\ zdisjoint (A, AGjm.MSv n) (ly_Q ly, kPtrArrayResv) /\
zdisjoint (A, AGjm.MSv n) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (A, AGjm.MSv n) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (A, AGjm.MSv n) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
{ repeat split; apply GAx; unfold static_extents, owned_extents, vis0_zones; rewrite !in_app_iff; cbn [In]; tauto. }
destruct (Z.eq_dec idx res) as [EQ|NE].
+ eapply (grantS_eq_em A); eassumption.
+ eapply (grantS_ne_em A); eassumption.
- rewrite EcM. apply YG0b.same_io_with_vm_backing.
Qed.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* sec_arms_em, the statement at the cgif model's bound MALLOC_MAX: sec_arms_w_em at NMAXW := MALLOC_MAX, NOBW :=
   ImgBaseAGS.NOB, ROOMW := 2 ^ 30, where the widened fields are AIfaceS's own (AGif4.AIfaceS_w). *)
Section fc.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the call's state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AGif0n.AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis IFS : AGif4.AIfaceS B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
Variable inst : Z.
Variable ly : alayout.
Variable S : astate.
Variable W : world tfibsegs.
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let INSTv : Z := bv_unsigned (getr regs0 11).
Let T : Z := ly_T ly.
Let Qb : Z := ly_Q ly.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hcf : bv_unsigned (getr regs0 15) = 0 \/ bv_unsigned (getr regs0 15) = 1.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hinst : 0x9d000 <= INSTv /\ INSTv + 0xe60 <= 0x1288a0 /\ INSTv mod 8 = 0.
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hnmax : n < nmax.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypothesis SV : AGif2.sview B W ly INSTv mem0 idx res.
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Htr : U tr S.
Hypothesis Hlive : blocks_bytes S + n <= lmax.
Variable regsU : bvmap 5 word.
(* The seed at Allocate's entry, at every block base [mb] (AGjx.SEED_ok holds for any mb: the seed does not mention
   the block); the prefix uses it at mb := 0, the grant arms at the granted base. *)
Hypothesis SEED : forall mb, st_ok tfibsegs (AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb) S_1
(restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
(* The errno add-on of AIfaceS (ErrnoGS.v): aes_post_grant is the errno fact at the grant leaf. *)
Hypothesis IFSE : ErrnoGS.AIfaceSE B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Lemma sec_arms_em :
amreal tfibsegs ((ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t stag n tr ob) (set_nev (st_nev S + 1) S)) W
(cfg_at tfibsegs A_Allocate regsU mem0 md0)
(alloc_leaf0_em B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n).
Proof using B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS TS inst ly S W regs0 mem0 md0 n tr
idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp Hgp Hra Hra4096 Hcf Hsp Htrlen Hso Hbp
Hinst Nrange Hnmax Hidx Hres Hidx_def Hres_def Hpres0 PBUF0 SV HARX HRP Htr Hlive regsU SEED IFSE.
exact (sec_arms_w_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS MALLOC_MAX ImgBaseAGS.NOB (2 ^ 30)
  (AGif4.ifs_apart _ _ _ _ _ _ _ _ _ _ _ _ IFS) (AGif4.ifs_grant _ _ _ _ _ _ _ _ _ _ _ _ IFS)
  (AGif4.ifs_room _ _ _ _ _ _ _ _ _ _ _ _ IFS)
  ltac:(unfold MALLOC_MAX, ImgBaseAGS.NOB; lia) ltac:(unfold MALLOC_MAX; vm_compute; discriminate) TS inst ly S W regs0 mem0 md0 n tr
  idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp Hgp Hra Hra4096 Hcf Hsp Htrlen Hso Hbp
  Hinst (AGi9.nrange_sec n Nrange) (proj2 Nrange) Hnmax Hidx Hres Hidx_def Hres_def Hpres0 PBUF0 SV HARX HRP Htr Hlive
  regsU SEED IFSE).
Qed.
End fc.
End d.
