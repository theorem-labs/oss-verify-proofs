(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGk0.v (a working branch 84ee52cd012, file sha256 5165b80b5ea7) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 14 image addresses moved by code-verified function pairs (10 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 1 code pcs the tool read as sizes, by the internal file funcpair.py); 3 hand maps (the internal file agreloc-resolve-A.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); 5 model labels (YG00 mcheck / spin tags) kept; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at d1f93c50c87) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc 0474699fc83547e0 (a working branch 83209f9d9cd8), --assume-source, --resolve the internal file resolve-102.txt (5 lines name this file); 9 numerals changed. *)
(* The SECONDARY arms of the frame-generic Allocate walk (n >= 64513, LargeMmapAllocator::Allocate), over the
   interfaces AGif0n.AIface and AGif4.AIfaceS.

   Ported from proofs/cgif/cgif_file_fuzzer/lib/YFk0.v, with the prefix of YFio.malloc_sec and the mmap node
   YFjs.nodeS, with the caller's frame made abstract and cgif's allocator relation replaced by the opaque [ARX]:
   - [sec_arms] starts at Allocate's entry with the model tree at the kernel's mmap ask (its caller has eaten the tick
     and the size check through ifs_shape, as AGioM.alloc_sec_w_em does before the memnorm twin AGk0M.sec_arms_w_em, AGioM.v:184-190); it runs AGjh.seg0, AGji.seg1 and the mmap node [node_sec];
   - [refuseS] is the ENOMEM arm (AGjj.segR, then ifs_post_null);
   - [grantS_ne] / [grantS_eq] are the grant arms (_eq also commits the next pointer-array page, AGjt.nodeV);
     their tail ends in [finEG] / [finOG] (AGif4.sfin), and the leaf comes from ifs_post_grant;
   - the depot callee is [D1W_gen], from ifs_depot.
   The leaf [QLEAF] is AGif4.alloc_leaf0 over the walk's virtual register file regs0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFhy AGhy AGhz AGi0 AGi4 AGi9 AB1h AGjm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h YG0j YG08 YF06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFia AFib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGid AGie AGif AGig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGjh AGji AGjj AGjn AGjo AGjk AGjl AGjp AGjq AGjr AGjt AGjz.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFi3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGjy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif2 AGif4.
(* The image-free interface layer (C5 / image split) is used qualified: importing ImgBaseAGS would hide AGjm's
   geometry names behind its copies. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AGif0n ImgBase ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0g YG0c.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Local Ltac step HR e :=
eapply SRr_bind; [exact e | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR].
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Instance-free helpers.                                                                                           *)
Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. lia. Qed.
Lemma SRr_with_AI : forall (Wx : world tfibsegs) cx (Q : world tfibsegs -> config -> Prop),
SRr tfibsegs Wx cx Q -> SRr tfibsegs Wx cx (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. intros Wx cx Q H HI T HK. apply (H HI T). intros W' c' Hle HI' HQ. exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Lemma amreal_askV : forall (q : kreq) (sN : astate) (Kc : Z -> itree astate (sptr * astate)) (Wx : world tfibsegs) (cx : config)
(Q : sptr * astate -> world tfibsegs -> config -> Prop),
match q with KDepot _ => False | _ => True end ->
SRr tfibsegs Wx cx (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok sN q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (Kc (bit i)) W1 (nx i) Q)) ->
amreal tfibsegs (IAsk q sN Kc) Wx cx Q.
Proof. intros q sN Kc Wx cx Q Hq H. destruct q; try (destruct Hq); cbn [amreal]; exact H. Qed.
Lemma lit_m1G : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1). Proof. apply bv_eq. reflexivity. Qed.
Lemma nores34G : mmap_noreserve_b (Z_to_bv 64 34) = false. Proof. reflexivity. Qed.
Lemma core34G : mmap_flags_core (Z_to_bv 64 34) = 34. Proof. reflexivity. Qed.
Lemma grant_anon_shapeG : forall (a k : word) md,
vm_maps (m_vmmaps (grant_md true (Z_to_bv 64 34) a k md)) = (a, k) :: vm_maps (m_vmmaps md) /\
vm_reserved (m_vmmaps (grant_md true (Z_to_bv 64 34) a k md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (grant_md true (Z_to_bv 64 34) a k md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (grant_md true (Z_to_bv 64 34) a k md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (grant_md true (Z_to_bv 64 34) a k md)) = vm_init_sp (m_vmmaps md) /\
grant_md true (Z_to_bv 64 34) a k md = mmap_model a k md.
Proof.
intros a k md. unfold grant_md, with_mmap_backing, mmap_model. rewrite nores34G.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn. repeat split; reflexivity.
Qed.
Lemma Hcut_outG : forall (Hh : word -> bool) lo hi (a : word), ~ (lo <= bv_unsigned a < hi) -> Hcut Hh lo hi a = Hh a.
Proof.
intros Hh lo hi a Ha. unfold Hcut. destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn [andb negb]; try (exfalso; lia);
rewrite ?andb_true_r, ?andb_false_r; try reflexivity; exfalso; apply Ha; lia.
Qed.
Lemma S_N_factsG : ss_pc S_N = 0x652bc /\ sr_get (ss_regs S_N) 17%bv = SLit 222 /\ sr_get (ss_regs S_N) 10%bv = SLit 0 /\ sr_get (ss_regs S_N) 11%bv = SOff aMS 0 /\
sr_get (ss_regs S_N) 12%bv = SLit 3 /\ sr_get (ss_regs S_N) 13%bv = SLit 34 /\ sr_get (ss_regs S_N) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs S_N) 15%bv = SLit 0 /\
no_cdata (ss_mem S_N) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The image-free names AGif4 states its records with (ImgBaseAGS / ImgBase, at cgif's instances AImg_A /
   AImgS_A) are the walk's own names by delta.  [ims] rewrites the former into the latter, so that lia / zlia see
   one atom where an interface fact meets a walk fact. *)
Lemma ims_MSv : ImgBaseAGS.MSv = AGjm.MSv. Proof. reflexivity. Qed.
Lemma ims_NDv : ImgBaseAGS.NDv = AGjm.NDv. Proof. reflexivity. Qed.
Lemma ims_N8D : ImgBaseAGS.N8D = AGjm.N8D. Proof. reflexivity. Qed.
Lemma ims_R8v : ImgBaseAGS.R8v = AGjm.R8v. Proof. reflexivity. Qed.
Lemma ims_QSv : ImgBaseAGS.QSv = AGjm.QSv. Proof. reflexivity. Qed.
Lemma ims_Kv : ImgBaseAGS.Kv = AGjm.Kv. Proof. reflexivity. Qed.
Lemma ims_Uv : ImgBaseAGS.Uv = AGjm.Uv. Proof. reflexivity. Qed.
Lemma ims_UEv : ImgBaseAGS.UEv = AGjm.UEv. Proof. reflexivity. Qed.
Lemma ims_SMv : ImgBaseAGS.SMv = AGjm.SMv. Proof. reflexivity. Qed.
Lemma ims_PBv : ImgBaseAGS.PBv = AGjm.PBv. Proof. reflexivity. Qed.
Lemma ims_SHBv : ImgBaseAGS.SHBv = AGjm.SHBv. Proof. reflexivity. Qed.
Lemma ims_WIN : ImgBaseAGS.WIN = AGjm.WIN. Proof. reflexivity. Qed.
Lemma ims_WINP : ImgBaseAGS.WINP = AGjm.WINP. Proof. reflexivity. Qed.
Lemma ims_WINT : ImgBaseAGS.WINT = AGjm.WINT. Proof. reflexivity. Qed.
Lemma ims_WINI : ImgBaseAGS.WINI = AGjm.WINI. Proof. reflexivity. Qed.
Lemma ims_AFSTACK : ImgBaseAGS.AFSTACK = AGhy.AFSTACK. Proof. reflexivity. Qed.
Lemma ims_DEP_STK : ImgBaseAGS.DEP_STK = AFl0.DEP_STK. Proof. reflexivity. Qed.
Lemma ims_NOB : ImgBaseAGS.NOB = YF06.NOB. Proof. reflexivity. Qed.
Lemma ims_dzone : ImgBaseAGS.ims_dzone = AGjm.DZONE. Proof. reflexivity. Qed.
Lemma ims_zone3 : ImgBaseAGS.ims_zone3 = zone3. Proof. reflexivity. Qed.
Lemma ims_img_end : ImgBaseAGS.ims_img_end = 0x600000. Proof. reflexivity. Qed.
Lemma ims_csh_end : ImgBaseAGS.ims_csh_end = 0x800b8000. Proof. reflexivity. Qed.
Lemma ims_shb : ImgBaseAGS.ims_shb = AGjm.SHBv. Proof. reflexivity. Qed.
Lemma ims_oom : ImgBase.im_oom = TFIB_OOM. Proof. reflexivity. Qed.
Lemma ims_errno : ImgBase.im_errno = TFIB_ERRNO. Proof. reflexivity. Qed.
Lemma ims_tsd : ImgBase.im_tsd = TFIB_TSD. Proof. reflexivity. Qed.
Local Ltac ims := rewrite ?ims_MSv, ?ims_NDv, ?ims_N8D, ?ims_R8v, ?ims_QSv, ?ims_Kv, ?ims_Uv, ?ims_UEv, ?ims_SMv, ?ims_PBv,
?ims_SHBv, ?ims_WIN, ?ims_WINP, ?ims_WINT, ?ims_WINI, ?ims_AFSTACK, ?ims_DEP_STK, ?ims_NOB, ?ims_dzone, ?ims_zone3, ?ims_oom, ?ims_errno.

(* ---------------------------------------------------------------------------------------------------------------- *)
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
(* The call site's three bounds (in this unit: [sec_arms] below, :1368, at cgif's constants; AGioM.alloc_sec_w_em, AGioM.v:66-69, for AGk0M's copy of this section): the size NMAXW, the instance's grant-existence bound NOBW
   (cgif: ImgBaseAGS.NOB = 2 ^ 29) and its room below the vm limit ROOMW (cgif: the model's VM_HEAD = 2 ^ 30).
   The walk asks the kernel for a map of MSv < n + 12296 bytes and exposes it with its shadow hull, so it needs
   the map inside NOBW, and 2 * MSv + MSv / 8 + 2 pages inside ROOMW plus, on the grow arm, the
   pointer-array commit's room of 2 ^ 19 (AGjt.nodeV). *)
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
Hypothesis Hinst : 0xa1000 <= INSTv /\ INSTv + 0xe60 <= 0x12d120 /\ INSTv mod 8 = 0.
(* The bound the walk files read (AGi9.SEC_NMAX = 2 ^ 29 - 4 pages), and the call site's (ifs_apart_w's). *)
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

(* The instance, its window and the walk's frame. *)
Lemma inst_rng : 0xa3e98 <= inst /\ inst + 0xe60 <= 0xa86e0 /\ inst mod 8 = 0.
Proof. exact (AGif0n.if_inst _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem0 md0 HARX). Qed.
Lemma INSTv_inst : bv_unsigned (getr regs0 11) = inst.
Proof. pose proof inst_rng as (I1 & I2 & _). rewrite Hi11. unfold YG0d.w64. apply unsigned_lit_small. lia. Qed.
Lemma Hinst_w : 0xa1000 <= INSTv /\ INSTv + 0xe60 <= 0x17cd88 /\ INSTv mod 8 = 0.
Proof. destruct Hinst as (H1 & H2 & H3). split; [exact H1|]. split; [lia | exact H3]. Qed.
Lemma WFR : AGImgA.wframe W ly regs0 mem0 tr.
Proof. split; [exact Hsp|]. split; [exact Htrlen|]. split; [exact Hso|]. split; [exact Hbp | exact Hpres0]. Qed.
Lemma aregs_of_RCS : forall regs' : bvmap 5 word,
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
aregs_preserved regs0 regs'.
Proof.
intros regs' RCS r Hr. apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(lia) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(lia) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(lia) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(lia) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(lia) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia) 27%bv eq_refl) ];
cbn [In]; tauto.
Qed.
Lemma same_io_wvb : forall md mat', same_io md0 md -> same_io md0 (with_vm_backing (m_vm_lazy md) mat' md).
Proof. intros md mat' (X1 & X2 & X3 & X4). unfold same_io in *. rewrite <- X1, <- X2, <- X3, <- X4. repeat split; reflexivity. Qed.

(* The model side: the leaf, the secondary body of sec_alloc after the mmap answer, and the depot step. *)
Definition DPOST (z : Z) (m : word -> option byte) : Prop := dpost inst ly S W tr z m.
Definition S1 : astate := set_nev (st_nev S + 1) S.
Definition QLEAF (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
AGif4.alloc_leaf0 B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n r W' c'.
Definition sec_body : M (option sptr) :=
s <- YG00.get ;;
mcheck (Z.of_nat (length (st_sec_arr s)) <? kMaxNumChunks) 9 ;;
YG00.put (set_secs (st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]) s) ;;
(if Z.of_nat (length (st_sec_arr s)) =? st_sec_reserved s then
z2 <- askz (KMapPtrArray (8 * Z.of_nat (length (st_sec_arr s))) kPtrArrayCommit) ;;
if aGranted z2 then YG00.modify (fun s0 => set_sec_reserved (st_sec_reserved s0 + kPtrArrayEntriesPerCommit) s0) else spin 11
else YG00.ret tt) ;;
YG00.modify (fun s0 => set_sec_arr (st_sec_arr s0 ++ [length (st_secs s)]) s0) ;;
YG00.ret (Some (PSec (length (st_secs s)) kPage)).
Definition KSEC (z : Z) : itree astate (sptr * astate) :=
(ob <- (if z =? 0 then YG00.ret None else sec_body) ;; ImgBaseAGS.malloc_K_t stag n tr ob) S1.
Lemma malloc_secondary_eq : forall s, from_primary n = false ->
malloc n tr s = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 3 ;; ob <- sec_alloc n ;; malloc_K n tr ob) s.
Proof. intros s FP. unfold malloc, malloc_K. rewrite FP. reflexivity. Qed.
Lemma sec_ask_eq : forall (Wx : world tfibsegs) c Q,
amreal tfibsegs ((ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t stag n tr ob) S1) Wx c Q = amreal tfibsegs (IAsk (KMmapSec (sec_map_size n)) S1 KSEC) Wx c Q.
Proof. intros Wx c Q. reflexivity. Qed.
Definition KDEP (s : astate) (beg : sptr) (z : Z) : itree astate (sptr * astate) :=
((if z =? 0 then YG00.ret tt
else (s' <- YG00.get ;;
mcheck (depot_ids s' + 1 <? kDepotIdsPerBlock) 14 ;;
mcheck (kStartFramesMax + depot_frames s' + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock) 13 ;;
YG00.put (set_depot (st_depot s' ++ [tr]) s'))) ;;
(let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;; if aGranted z then YG00.ret tt else spin stag else YG00.ret tt) ;;
YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) k) s0) ;;
YG00.ret (ck_user k))) s.
Lemma malloc_K_some : forall beg s (Wx : world tfibsegs) c Q,
amreal tfibsegs (ImgBaseAGS.malloc_K_t stag n tr (Some beg) s) Wx c Q = SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot tr) z /\ amreal tfibsegs (KDEP s beg z) W1 c1 Q).
Proof. intros. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk at a block base [mb]: sec_arms uses mb := 0 before the grant and mb := the granted base after it.      *)
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
(* The map of a request below NMAXW is at most NMAXW + 3 pages (MSv < n + 12296), so it fits the instance's
   grant-existence bound NOBW and, with its shadow hull, the instance's room ROOMW. *)
Lemma MSBW_g : 0 < AGjm.MSv n <= NMAXW + 4 * 4096.
Proof using n NMAXW Nrange HnW. pose proof (AGjm.size_facts n Nrange) as (Z1 & Z2 & Z3 & _ & _ & _ & Z7 & Z8 & _ & Z10 & _). clear - Z1 Z3 Z7 Z8 Z10 HnW. lia. Qed.
Lemma MS8_g : AGjm.MSv n / 8 <= (NMAXW + 4 * 4096) / 8.
Proof using n NMAXW Nrange HnW. apply Z.div_le_mono; [reflexivity | exact (proj2 MSBW_g)]. Qed.
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
Lemma at_S_wvb : forall (Wx : world tfibsegs) md mat X P ss W' c',
at_S Wx (with_vm_backing (m_vm_lazy md) mat md) X P ss W' c' -> at_S Wx md X P ss W' c'.
Proof. intros Wx md mat X P ss W' c' (-> & ms & mat' & E' & -> & HE & HS & MEQ & PRS & HP). split; [reflexivity|]. exists ms, mat', E'. rewrite wvb_collapse. split; [reflexivity|]. repeat (split; [assumption|]). exact HP. Qed.
Lemma pru_MS : page_round_up_Z MSv = MSv.
Proof.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). unfold page_round_up_Z, page_size.
apply Z.mod_divide in Z9 as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia.
rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia.
Qed.
Lemma SH_hull : forall A, AGif4.SHLO A <= shadow_addr A /\ shadow_addr A + MSv / 8 <= AGif4.SHHI A MSv /\
AGif4.SHHI A MSv - AGif4.SHLO A <= MSv / 8 + 8192 /\
AGif4.SHLO A mod 4096 = 0 /\ AGif4.SHHI A MSv mod 4096 = 0 /\ AGif4.SHLO A <= AGif4.SHHI A MSv.
Proof.
intros A. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). unfold AGif4.SHLO, AGif4.SHHI.
pose proof (Z.div_mod (shadow_addr A) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (shadow_addr A) 4096 ltac:(lia)) as B1.
pose proof (Z.div_mod (shadow_addr A + MSv / 8 + 4095) 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (shadow_addr A + MSv / 8 + 4095) 4096 ltac:(lia)) as B2.
repeat split; first [apply Z_mod_mult | lia].
Qed.

(* The refusal arm: the kernel answered ENOMEM. *)
Lemma segR_ : forall W' c',
at_S W md0 WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W' c' ->
SRr tfibsegs W' c' (at_RETS W (w64 0) md0 WINPN PNULLX).
Proof. pose proof (SEED mb) as SEEDm. intros W' c' H. eapply AGjj.segR; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Theorem refuseS : forall (mat : list word) c',
at_S W (with_vm_backing (m_vm_lazy md0) mat md0) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
amreal tfibsegs (KSEC 0) W c' QLEAF.
Proof.
intros mat c' HR. change (amreal tfibsegs (KSEC 0) W c' QLEAF) with (SRr tfibsegs W c' (QLEAF (PNull, S1))).
apply at_S_wvb in HR. eapply SRr_mono; [exact (segR_ _ _ HR)|].
intros W2 c2 _ (-> & regs' & mem' & mat2 & -> & R10 & RCS & MEQ & PRS & ((HB & VOOM) & (Vunw & Vres & Vnch & Vmtx & PRT & VISI))).
pose proof INSTv_inst as EI.
assert (SN : AGif4.snull W ly regs0 mem0 inst n (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) 0 regs' mem').
{ constructor.
  - exact R10.
  - exact RCS.
  - intros x N1 N2 N3. apply MEQ. intros [X|[X|X]]; [exact (N1 X) | apply N2; rewrite ims_oom; lia | exact (N3 X)].
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
split. { rewrite R10. cbn [fst sptr_addr sptr_exp aeval]. reflexivity. }
split; [exact HLP|].
intros _. exact VOOM.
Qed.

(* The mmap node: the generic twin of YFjs.nodeS, its model steps from ifs_mwf / ifs_room / ifs_grant. *)
Lemma node_sec : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfibsegs -> config -> Prop) (c1 : config),
at_N W md0 WINP PBUF S_N W c1 -> AI tfibsegs (w_H W) (w_A W) (cfg_model c1) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMmapSec MSv) z) ->
(forall c', at_S W (cfg_model c1) WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W c' ->
amreal tfibsegs (K 0) W c' Q) ->
(forall (a : word) (W3 : world tfibsegs) (ms : machine_state) (E' : env),
let A := bv_unsigned a in let md2 := mmap_model a (w64 MSv) (cfg_model c1) in
grant_ok_na_pin (cfg_model c1) a MSv = true ->
wle W W3 -> hsub (w_H W3) (w_H W) -> (forall x : word, w_H W x = false -> w_H W3 x = false) ->
w_A W3 = (AGif4.SHLO A, AGif4.SHHI A MSv) :: (A, A + MSv) :: w_A W ->
(forall x : word, A <= bv_unsigned x < A + MSv -> w_H W3 x = false) ->
(forall x : word, AGif4.SHLO A <= bv_unsigned x < AGif4.SHHI A MSv -> w_H W3 x = false) ->
(forall x : word, ~ (A <= bv_unsigned x < A + MSv) -> ~ (AGif4.SHLO A <= bv_unsigned x < AGif4.SHHI A MSv) -> w_H W3 x = w_H W x) ->
AI tfibsegs (w_H W3) (w_A W3) md2 -> amwf md2 -> same_io md0 md2 -> eager_used md2 <= eager_used (cfg_model c1) + MSv ->
vm_maps (m_vmmaps md2) = (a, w64 MSv) :: vm_maps (m_vmmaps (cfg_model c1)) /\
vm_reserved (m_vmmaps md2) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md2) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md2) = vm_mmap_base (m_vmmaps (cfg_model c1)) /\
vm_init_sp (m_vmmaps md2) = vm_init_sp (m_vmmaps (cfg_model c1)) ->
env_agree sHAV E0 E' -> st_ok_ecall tfibsegs E' S_N (restrict (w_H W) ms) ->
(forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall y, sp0 - AFSTACK <= y < sp0 -> apresent (w_H W) (ms_mem ms) y) -> PBUF (ms_mem ms) ->
amreal tfibsegs (K 1) W3 (mkCfg (mkst (regupd (ms_regs ms) 10%bv a) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill a (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md2) Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H W) (w_A W) (cfg_model c1) -> AI tfibsegs (w_H W) (w_A W) (cfg_model (nx i))) /\
(forall i, aok sN (KMmapSec MSv) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H W) (w_A W) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) W (nx i) Q).
Proof.
intros RT sN K Q c1 HN HAI Haok KEEP GRANT IO0.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
pose proof (AGif4.ifs_mwf _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 HARX) as MW.
pose proof (AGif4.ifs_room _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 n HARX HRP) as ROOM.
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md0) mat md0) in *.
assert (EcM : cfg_model c1 = mdN) by (rewrite Ec; reflexivity). rewrite EcM in *.
assert (MWN : amwf mdN) by (exact (amwf_same md0 mdN (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW)).
assert (MWF0 : MWF mdN) by (apply (proj1 (amwf_MWF mdN)); exact (proj1 MWN)).
destruct (st_ok_ecall_shape_r tfibsegs (w_H W) E' S_N ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (HEn : forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
pose proof S_N_factsG as (Hpc & H17 & H10 & H11 & H12 & H13 & H14 & H15 & Hnc).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (rewrite (Hregs 17%bv), H17; reflexivity).
assert (R10 : getr regs 10 = Z_to_bv 64 0) by (rewrite (Hregs 10%bv), H10; reflexivity).
assert (R11 : getr regs 11 = Z_to_bv 64 MSv).
{ rewrite (Hregs 11%bv), H11, sv_denot_SOff0. unfold aMS. rewrite (HEn 42%nat ltac:(unfold sHAV; lia)). exact EaMS. }
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (rewrite (Hregs 12%bv), H12; reflexivity).
assert (R13 : getr regs 13 = Z_to_bv 64 34) by (rewrite (Hregs 13%bv), H13; reflexivity).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; apply lit_m1G).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (rewrite (Hregs 15%bv), H15; reflexivity).
assert (MSB : 0 < MSv <= SEC_NMAX + 4 * 4096) by (clear - Z8 Z1 Z2 Z3; unfold SEC_NMAX in *; lia).
(* the map is at most n + 3 pages, so it is inside the instance's bounds NOBW and ROOMW *)
pose proof MSBW_g as MSBW. pose proof MS8_g as MS8.
destruct (IFG inst ly S W mem0 md0 mat MSv HARX ltac:(clear - MSBW HNOB; lia)) as [a0 Ha0].
assert (SL0 : eager_used mdN + A_bytes (w_A W) + ROOMW <= vm_limit (m_vmmaps mdN))
by (unfold mdN; rewrite eager_used_wvb, m_vmmaps_wvb; exact (IFR inst ly S W mem0 md0 n HARX HRP)).
assert (PER : forall a : word, grant_ok_na_pin mdN a MSv = true ->
(AI tfibsegs (w_H W) (w_A W) (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) /\ MWF (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN)) /\
mmap_noreserve_backed_ok (Z_to_bv 64 34) mdN MSv = true /\
eager_used (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) <= eager_used mdN + MSv /\
maps_nonempty (grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN)).
{ intros a Ha. pose proof (AFia.grant_parts mdN a MSv Ha) as (Pal & Ppos & Pce & Prf & Ppl).
assert (CE : bv_unsigned a + page_round_up_Z MSv <= alloc_top (m_vmmaps mdN)) by (rewrite pru_MS; exact Pce).
assert (PL' : region_free (vm_reserved (m_vmmaps mdN) ++ vm_maps (m_vmmaps mdN)) a (Z_to_bv 64 (page_round_up_Z MSv)) = true) by (rewrite pru_MS; exact Prf).
assert (SL1 : eager_used mdN + A_bytes (w_A W) + page_round_up_Z MSv <= vm_limit (m_vmmaps mdN)) by (rewrite pru_MS; clear - SL0 MSBW HROOM MS8; lia).
pose proof (commit_AI tfibsegs (w_H W) (w_A W) mdN true (Z_to_bv 64 34) a MSv HAI MWF0 nores34G ltac:(unfold page_size; exact Pal) (proj1 MSB) CE PL' SL1) as [CG BUDg].
pose proof (commit_eager tfibsegs (w_H W) (w_A W) mdN true (Z_to_bv 64 34) a MSv HAI MWF0 nores34G ltac:(unfold page_size; exact Pal) (proj1 MSB) CE PL' SL1) as EG.
pose proof (commit_nonempty true (Z_to_bv 64 34) a (Z_to_bv 64 (page_round_up_Z MSv)) mdN ltac:(rewrite pru_MS; unfold w64; rewrite unsigned_lit_small by (clear - MSB; unfold SEC_NMAX in MSB; lia); exact (proj1 MSB)) (proj2 MWN)) as NZg.
rewrite pru_MS in CG, BUDg, EG, NZg. fold (w64 MSv) in CG, EG, NZg. exact (conj CG (conj BUDg (conj EG NZg))). }
destruct (PER a0 Ha0) as (_ & BUD0 & _).
destruct (anon_node tfibsegs regs (Z_to_bv 64 0x652bc) mem (seg_rom tfibsegs) mdN (Z_to_bv 64 34) MSv
(AI_halted _ _ _ _ HAI) R17 R10 R11 ltac:(clear - MSB; unfold SEC_NMAX in MSB; lia) R12 R13 core34G R14 R15
ltac:(rewrite pru_MS; exists a0; exact Ha0) ltac:(rewrite pru_MS; exact BUD0)) as (I & nx & bit & ga & i0 & NODE & Bi0 & OUT).
rewrite pru_MS in OUT. fold (w64 MSv) in OUT.
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, bit, (fun _ => false), i0.
split. { rewrite Ec, Hms, Hpc. exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & _ & Hg & -> & ->); cbn [cfg_model]; exact (proj1 (proj1 (PER (ga i) Hg))). }
split. { intros i. apply Haok. destruct (OUT i) as (md_i & _ & _ & Bv & _); clear - Bv; lia. }
split; [reflexivity|]. split; [exact Bi0|]. split; [intros i _; destruct (OUT i) as (md_i & _ & _ & Bv & _); exact Bv|].
split; [intros i E; discriminate E|].
intros i _. destruct (OUT i) as (md_i & Hh_i & IO_i & Bv & Hg & NX & MD); rewrite Bv, NX; rewrite MD in IO_i |- *.
set (a := ga i) in *. set (A := bv_unsigned a) in *.
destruct (PER a Hg) as ([AIg MWFg] & _ & EG & NZg).
pose proof (grant_anon_shapeG a (w64 MSv) mdN) as (SH1 & SH2' & SH3 & SH4' & SH4i & SH5').
set (md2 := grant_md true (Z_to_bv 64 34) a (w64 MSv) mdN) in *.
pose proof (AFia.grant_parts mdN a MSv Hg) as (Pal & Ppos & Pce & Prf & Ppl).
fold A in Pal, Ppos, Pce.
pose proof (SH_hull A) as (UH1 & U2 & U3 & U4 & U5 & U6).
assert (AL1 : A <= A + MSv) by (clear - MSB; lia).
assert (AL2 : A mod page_size = 0) by (unfold page_size; exact Pal).
assert (AL3 : (A + MSv) mod page_size = 0).
{ unfold page_size. clear - Pal Z9. apply Z.mod_divide in Pal as [q' Hq]; [|lia]. apply Z.mod_divide in Z9 as [r' Hr]; [|lia]. rewrite Hq, Hr. apply Z.mod_divide; [lia|]. exists (q' + r'). lia. }
destruct (allow_expose tfibsegs W md2 A (A + MSv) AL1 AL2 AL3 AIg ltac:(rewrite SH3; clear - EG SL0 MSBW HROOM MS8; lia))
as (LE2 & A2 & AB2 & VIS2 & MON2 & AI2).
set (W2 := wallow tfibsegs W A (A + MSv) AL1 AL2 AL3) in *.
assert (SL2 : AGif4.SHLO A mod page_size = 0) by (unfold page_size; exact U4).
assert (SL3 : AGif4.SHHI A MSv mod page_size = 0) by (unfold page_size; exact U5).
assert (BUD3 : eager_used md2 + A_bytes (w_A W2) + (AGif4.SHHI A MSv - AGif4.SHLO A) <= vm_limit (m_vmmaps md2)).
{ rewrite SH3, AB2. clear - EG SL0 MSBW HROOM MS8 U3. lia. }
destruct (allow_expose tfibsegs W2 md2 (AGif4.SHLO A) (AGif4.SHHI A MSv) U6 SL2 SL3 AI2 BUD3)
as (LE3 & A3 & AB3 & VIS3 & MON3 & AI3).
set (W3 := wallow tfibsegs W2 (AGif4.SHLO A) (AGif4.SHHI A MSv) U6 SL2 SL3) in *.
assert (MON : forall x : word, w_H W x = false -> w_H W3 x = false) by (intros x Hx; apply MON3, MON2, Hx).
assert (SUB : hsub (w_H W3) (w_H W)).
{ intros x Hx. destruct (w_H W x) eqn:Ex; [reflexivity|]. rewrite (MON x Ex) in Hx. discriminate Hx. }
eapply (amreal_world_le tfibsegs _ W W3); [exact (wle_trans _ _ _ _ LE2 LE3) | intros _; exact AI3 |].
change (with_mmap_backing (Z_to_bv 64 34) a (w64 MSv) (mmap_model a (w64 MSv) mdN)) with md2.
pose proof (GRANT a W3 ms E' Hg (wle_trans _ _ _ _ LE2 LE3) SUB MON) as G. cbv zeta in G. rewrite <- SH5' in G. fold md2 in G. fold A in G.
rewrite Hms in G. cbn [ms_regs ms_mem pend_at] in G. apply G; clear G.
- rewrite A3, A2. reflexivity.
- intros x Hx. apply MON3. apply VIS2. exact Hx.
- exact VIS3.
- intros x N1 N2. unfold W3, W2, wallow. cbn [w_H]. rewrite (Hcut_outG _ (AGif4.SHLO A) (AGif4.SHHI A MSv) x) by exact N2. apply Hcut_outG. exact N1.
- exact AI3.
- split; [apply (proj2 (amwf_MWF md2)); exact MWFg | exact NZg].
- exact (IOtr _ IO_i).
- exact EG.
- rewrite SH1, SH2', SH3, SH4', SH4i. repeat split; reflexivity.
- exact HE.
- rewrite Hms in HS. exact HS.
- intros x Hx. rewrite <- (MEQ x Hx), Hms. reflexivity.
- intros y Hy. rewrite Hms in PRS. exact (PRS y Hy).
- rewrite Hms in HPm. exact HPm.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The grant arms, at the granted base [mb].                                                                        *)
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

(* The granted base, its range and its apartness (ifs_apart). *)
Lemma mb_range : 0 <= mb < 2 ^ 64.
Proof. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
clear - M1 M2 Z8 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia. Qed.
Lemma Umb : bv_unsigned (w64 mb) = mb.
Proof. pose proof mb_range as R. unfold YG0d.w64. apply unsigned_lit_small. exact R. Qed.
Lemma MSB : 0 < MSv <= SEC_NMAX + 4 * 4096.
Proof. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _). clear - Z8 Z1 Z2 Z3. unfold SEC_NMAX in *. zlia. Qed.
Lemma APART : zone3 mb MSv /\ Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) /\
(forall g, g mod 8 = 0 -> mb <= g -> g + 8 <= mb + MSv -> mem0 (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0)).
Proof.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _).
pose proof (IFA inst ly S W mem0 md0 mat MSv (w64 mb) HARX MSBW_g Z9 GOK) as X. rewrite Umb in X. exact X.
Qed.
Lemma GAP : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Proof. exact (proj1 (proj2 APART)). Qed.
Lemma HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096).
Proof. apply (proj1 (Forall_forall _ _) GAP). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto. Qed.
Lemma SHZ : forall a, SMv <= a < SMv + MSv / 8 -> w_H W3 (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof (SH_hull mb) as (H1 & H2 & _).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
split; [apply VISH3; unfold w64; rewrite unsigned_lit_small by exact Ra; rewrite SMA in Ha; clear - Ha H1 H2 MZ; zlia|].
set (g := mb + 8 * (a - SMv)).
assert (Hg : shadow_addr g = a).
{ subst g. rewrite SMA. unfold shadow_addr. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp.
replace (p * 4096) with (p * 512 * 8) by zlia. rewrite (Z.div_mul (p * 512) 8) by zlia.
replace (p * 512 * 8 + 8 * (a - (SHADOW_OFF + p * 512))) with ((p * 512 + (a - (SHADOW_OFF + p * 512))) * 8) by zlia.
rewrite Z.div_mul by zlia. zlia. }
rewrite <- Hg. unfold w64. rewrite MEQ.
- pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8. assert (M8 : MSv mod 8 = 0) by (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|zlia]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; apply Z.mod_mul; zlia).
apply (proj2 (proj2 APART) g).
+ subst g. apply Z.mod_divide; [zlia|]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. exists (p * 512 + (a - SMv)). zlia.
+ subst g. clear - Ha MZ. zlia.
+ subst g. clear - Ha DM8 M8 MZ. zlia.
- rewrite unsigned_lit_small by (rewrite Hg; exact Ra). rewrite Hg. intros Hw. unfold AGjm.WINP, AGjm.WINT, AGjm.WINI in Hw. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _).
pose proof Hinst as HIN. destruct Hsp as (S1' & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
clear - Hw Ha SM1 SM2 F1 S1' T7 HBS HIN MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, AFSTACK, t_unwinding, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *.
try unfold INSTv in *. try unfold sp0 in *. try unfold T in *. zlia.
Qed.
Lemma VISM : forall a, mb <= a < mb + MSv -> w_H W3 (w64 a) = false.
Proof. intros a Ha. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. apply VISM3. unfold w64. rewrite unsigned_lit_small; [exact Ha | clear - Ha M1 M2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia]. Qed.
(* The committed pointer-array slot is present (the view's sv_qarr). *)
Lemma QSP3 : idx <> res -> QSP W3 (zfill (w64 mb) (w64 MSv) (ms_mem ms)).
Proof.
intros NE u Hu. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRA].
assert (Ru : TFIB_IMG_END <= u < 2 ^ 64) by (clear - Hu F9 F10 HI HRS MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AGjm.QSv, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
assert (P0 : apresent (w_H W) mem0 u).
{ apply (AGif2.sv_qarr _ _ _ _ _ _ _ SV). unfold AGjm.QSv in Hu. try unfold Qb in Hu. clear - Hu HI HRS NE. lia. }
destruct P0 as [Hh [b Hb']]. split; [exact (MON3 _ Hh)|]. exists b. rewrite zfill_out.
- rewrite MEQ; [exact Hb'|]. rewrite unsigned_lit_small by (clear - Ru MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in Ru; zlia).
unfold AGjm.WINP, AGjm.WINT, AGjm.WINI. pose proof BSLv_range as HBS. pose proof high_facts as (F1 & _). pose proof Hinst as HIN. destruct Hsp as (S1' & _ & S3' & _).
pose proof stack_ivs as (_ & _ & _ & SI4). pose proof HCX as (_ & _ & QT & _). unfold zdisjoint in QT. cbn [fst snd] in QT.
clear - Hu F1 F9 F10 HI HRS HBS HIN S1' S3' SI4 QT MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AGjm.QSv, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, AFSTACK, t_unwinding, kThreadObjSize, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *.
try unfold Qb in *. try unfold T in *. try unfold sp0 in *. try unfold INSTv in *. zlia.
- rewrite Umb. unfold w64. rewrite !unsigned_lit_small by (clear - Ru M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, SEC_NMAX in *; zlia).
destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ. clear - Hu MQ HI HRS F9 F10 MZ. unfold AGjm.QSv, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.

(* The depot callee (ifs_depot): the const-cell zone the walk leaves alone, then the callee at any later world. *)
Lemma CZS_untouched : forall a, AGif4.CZS ly inst a -> 0 <= a < 2 ^ 64 /\ ~ WIN a /\ ~ QR a.
Proof.
intros a Ha. pose proof INSTv_inst as EI. pose proof inst_rng as (HIN & HIN2 & _).
pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof stack_ivs as (SI1 & SI2 & SI3 & SI4). pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & QNB & QSB & _ & _ & CNB & CSB).
pose proof HCX as (CP & CT & QT & CQ). destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
pose proof Hidx as HI. pose proof Hres as [HRS _]. destruct Hmap_apart as (MT & MC & _ & MQ & _). pose proof HmapD as MD. pose proof BSLv_range as HBS.
unfold zdisjoint in TNB, TSB, QNB, QSB, CNB, CSB, CP, CT, QT, CQ, MT, MC, MQ, MD. cbn [fst snd] in TNB, TSB, QNB, QSB, CNB, CSB, CP, CT, QT, CQ, MT, MC, MQ, MD.
pose proof (pairwise_ij _ _ 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DT. pose proof (pairwise_ij _ _ 4 2 _ _ (lo_disj ly LY) eq_refl eq_refl) as DNB.
pose proof (pairwise_ij _ _ 5 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSB. pose proof (pairwise_ij _ _ 1 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQD.
pose proof (pairwise_ij _ _ 7 0 _ _ (lo_disj ly LY) eq_refl eq_refl) as DSTK.
pose proof (Forall_nth' _ _ 7 _ (lo_app ly LY) eq_refl) as DH. cbv beta in DH.
pose proof (pairwise_ij _ _ 7 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as DIMG.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(zlia) DH DIMG) as DZ3. unfold in_app in DH.
unfold zdisjoint in DT, DNB, DSB, DQD, DSTK. cbn [fst snd] in DT, DNB, DSB, DQD, DSTK, DH.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH.
pose proof (zone3_apart_img _ _ a F7) as CI. pose proof (zone3_apart_hsh _ _ a F7) as CH.
pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH.
pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH.
pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH.
pose proof (zone3_apart_img _ _ a DZ3) as DI. pose proof (zone3_apart_hsh _ _ a DZ3) as DHH.
pose proof (zone3_apart_img _ _ a (AGjm.mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (AGjm.mzone_zone3 _ _ (proj2 Hmap))) as MH.
destruct F1 as (T4096 & _). destruct F7 as (C4096 & _). destruct F9 as (Q4096 & _).
unfold AGif4.CZS in Ha. rewrite ims_img_end, ims_shb, ims_csh_end, ims_tsd in Ha. unfold AGjm.SHBv in Ha.
unfold AGjm.WIN, AGjm.WINT, AGjm.WINI, AGjm.WINM, AGjp.QR, TFIB_TSD in *. numconst.
unfold kPtrArrayResv, kPtrArrayEntriesPerCommit, kMaxNumChunks, kCtxMapSize, kHighShadowBeg, kHighShadowEnd, SEC_NMAX, t_unwinding,
o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. unfold AGjm.QSv in *.
try rewrite !EI in *. try unfold T in *. try unfold Qb in *. try unfold sp0 in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
- clear - Ha HI HRS HBS S1 S3 T4 T7 TI QI NI BI MI SM1 MZ HIN HIN2 EI. split; [clear - Ha MZ HIN HIN2; zlia|]. split; [|zlia]. intros HW.
try rewrite !EI in HW. try rewrite !EI in HBS.
destruct HW as [HW|[HW|[HW|HW]]]; [zlia | zlia | | zlia]. destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]; zlia.
- clear - Ha HI HRS HBS S1 S3 T4 T7 TH QH NH BH MH SM1 MZ HIN HIN2 EI. try rewrite !EI in HBS. repeat split; zlia.
- clear - Ha F2 T4096 QT MT SI1 TNB TSB HI HRS SM1 SM2 HBS TI TH MZ HIN HIN2 EI. try rewrite !EI in HBS. repeat split; zlia.
- clear - Ha F8 C4096 CQ MC SI3 CNB CSB CT HI HRS SM1 SM2 HBS CI CH MZ HIN HIN2 EI. try rewrite !EI in HBS. repeat split; zlia.
- clear - Ha HI HRS HBS S1 S3 T4 T7 TI QI NI BI MI SM1 MZ HIN HIN2 EI. try rewrite !EI in HBS. repeat split; zlia.
- clear - Ha DH DT DQD MD DSTK DNB DSB DI DHH HI HRS SM1 SM2 Z8 HBS S1 S3 MZ HIN HIN2 EI. try rewrite !EI in HBS. repeat split; zlia.
Qed.
Lemma D1W_gen : forall (Wy : world tfibsegs), (forall x : word, w_H W x = false -> w_H Wy x = false) ->
forall (X : Z -> Prop) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
(forall a, X a -> WIN a \/ QR a) ->
getr regs 10 = Z_to_bv 64 BPv -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x32964 ->
bv_unsigned (getr regs 2) = sp0 - 128 ->
PBUFW Wy mem -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H Wy) mem a) ->
(forall x : word, ~ X (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wy) mem (INSTv + o_sec_mutex + k) = Some 0) ->
SRr tfibsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x32964) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 128 - DEP_STK <= bv_unsigned x < sp0 - 128) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
DPOST z mem').
Proof.
intros Wy MONy X regs mem md HXQ R10 R11 R3 R4 R1 Rsp BUF PRES MEQ' MUT0.
pose proof INSTv_inst as EI.
pose proof Hsp as (S1' & S2' & S3' & S4'). pose proof Hbp as (BP1 & BP2 & BP3).
assert (MEQa : forall a, 0 <= a < 2 ^ 64 -> ~ WIN a -> ~ QR a -> mem (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha N1 N2. apply MEQ'. rewrite unsigned_lit_small by exact Ha. intros HX. destruct (HXQ a HX) as [H|H]; [exact (N1 H) | exact (N2 H)]. }
eapply SRr_mono.
{ apply (AGif4.ifs_depot _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 tr Wy regs mem md BPv HARX Htr MONy).
- intros x Hx. rewrite ims_dzone in Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  assert (NWQ : ~ WIN (bv_unsigned x) /\ ~ QR (bv_unsigned x)).
  { destruct Hx as [Hd|Hc].
    - split; [exact (proj1 (DZONE_disj _ Hd))|].
      pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _).
      pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof Hres as [HRS _]. pose proof Hidx as HI.
      unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB. unfold AGjp.QR. clear - Hd QNB QSB F9 HRS HI.
      unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AGjm.DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia.
    - pose proof (CZS_untouched _ Hc) as (_ & N1 & N2). exact (conj N1 N2). }
  rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (MEQa _ Rx (proj1 NWQ) (proj2 NWQ)).
- intros k Hk. rewrite <- EI. exact (MUT0 k Hk).
- exact R10.
- exact R11.
- rewrite R3, Hgp. reflexivity.
- exact R4.
- rewrite R1. apply ret_ok_even. reflexivity.
- exact BUF.
- exact BP3.
- clear - S1' BP1. unfold AFSTACK in *. zlia.
- exact BP2.
- right. rewrite Rsp. clear - BP1. zlia.
- rewrite Rsp. apply Z.mod_divide; [zlia|]. pose proof S4' as S4''. apply Z.mod_divide in S4'' as [q Hq]; [|zlia]. exists (q - 8). zlia.
- rewrite Rsp. unfold DEP_STK, AFSTACK, ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *. zlia.
- rewrite Rsp. zlia.
- rewrite Rsp. intros a Ha. apply PRES. unfold DEP_STK, AFSTACK, ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *. zlia. }
intros W' c' _ (-> & z & regs' & mem' & mat' & -> & RP & FR & PR' & DP). split; [reflexivity|].
exists z, regs', mem', mat'. split; [rewrite R1; reflexivity|]. split; [exact RP|].
split; [| split; [exact PR' | exact DP]].
intros x N1 N2. apply FR; [rewrite Rsp; exact N1 | exact N2].
Qed.

(* The segments of the grant arms, at this block base (AGjr .. AGjt). *)
Lemma grant_cont_ : forall (Wy : world tfibsegs) (md' : Model) (R : (word -> option byte) -> Prop),
hsub (w_H Wy) (w_H W) ->
(forall a, mb <= a < mb + MSv -> w_H Wy (w64 a) = false) ->
(forall a, SMv <= a < SMv + MSv / 8 -> w_H Wy (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0)) ->
R (zfill (w64 mb) (w64 MSv) (ms_mem ms)) ->
at_S Wy md' WIN (PSR Wy SH0 R) S_P0 Wy
(mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md').
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjr.grant_cont; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segG1_ : forall (Wy : world tfibsegs) (md1 : Model) (R : (word -> option byte) -> Prop), rstable R ->
forall c, at_S Wy md1 WIN (PSR Wy SH0 R) S_P0 Wy c -> SRr tfibsegs Wy c (at_S Wy md1 WIN (PSR Wy SH2 R) S_X).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjk.segG1; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segNE_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX -> idx <> res ->
forall c, at_S Wy md1 WIN (PSR Wy SH2 (QSPX Wy RX)) S_X Wy c -> SRr tfibsegs Wy c (at_S Wy md1 WIN (PSR Wy SH2 RX) S_YJ).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjl.segNE; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segEQa_ : forall (Wy : world tfibsegs) (md1 : Model) (R : (word -> option byte) -> Prop), rstable R -> pstable WIN1T R -> idx = res ->
forall c, at_S Wy md1 WIN (PSR Wy SH2 R) S_X Wy c -> SRr tfibsegs Wy c (at_N Wy md1 WIN (PSR Wy SH2 R) S_V).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjl.segEQa; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segJ_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) S_YJ Wy c -> SRr tfibsegs Wy c (at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjl.segJ; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segT1_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0 Wy c -> SRr tfibsegs Wy c (at_S Wy md1 X (PSR Wy SH2 RX) T_PD).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjp.segT1; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma at_S_depot_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX -> pstable DX RX ->
(forall x : word, w_H W x = false -> w_H Wy x = false) ->
forall (X : Z -> Prop), (forall a, X a -> WIN a \/ QR a) -> (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) T_PD Wy c ->
SRr tfibsegs Wy c (fun W2 c2 => exists z, at_S Wy md1 (fun a => X a \/ DX a) (PSR Wy SH2 (PDX Wy RX z)) T_2 W2 c2).
Proof. pose proof (SEED mb) as SEEDm. intros Wy md1 RX RXs RXt RXd MONy X HXQ HXW c HR. pose proof (D1W_gen Wy MONy) as D1w. eapply AGjp.at_S_depot; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segT2_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop) z, (forall a, WIN a -> X a) ->
forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX Wy RX z)) T_2 W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjp.segT2; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segU1_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop) z, (forall a, WIN a -> X a) -> N8D / 8 < 18446744073709551615 ->
forall W' c, at_S Wy md1 X (PSR Wy SH4 (PDX Wy RX z)) T_R W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjq.segU1; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segUe_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop) z, (forall a, WIN a -> X a) -> N8D / 8 < 18446744073709551615 -> bv_unsigned (getr regs0 15) <> 0 -> n mod 8 = 0 ->
forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH6 (PDX Wy RX z)) Ue_RET).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjq.segUe; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segUo_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop) z, (forall a, WIN a -> X a) -> N8D / 8 < 18446744073709551615 -> bv_unsigned (getr regs0 15) <> 0 -> n mod 8 <> 0 ->
forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PT Wy SH6o (PDX Wy RX z)) Uo_RET).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjq.segUo; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
(* can_fill = 0 (calloc): no fill, the same tail (AGjq.segUe0 / segUo0). *)
Lemma segUe0_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop) z, (forall a, WIN a -> X a) -> N8D / 8 < 18446744073709551615 -> bv_unsigned (getr regs0 15) = 0 -> n mod 8 = 0 ->
forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) Ue_RET0).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjq.segUe0; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma segUo0_ : forall (Wy : world tfibsegs) (md1 : Model) (RX : (word -> option byte) -> Prop), rstable RX -> pstable WIN1T RX ->
forall (X : Z -> Prop) z, (forall a, WIN a -> X a) -> N8D / 8 < 18446744073709551615 -> bv_unsigned (getr regs0 15) = 0 -> n mod 8 <> 0 ->
forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX Wy RX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PT Wy SH5o (PDX Wy RX z)) Uo_RET0).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjq.segUo0; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma QR_facts_ : idx = res -> QSv = Qb + 8 * res /\ QSv mod 131072 = Qb mod 131072 /\ QSv mod 4096 = 0 /\ (4096 <= Qb <= QSv /\ zone3cases Qb kPtrArrayResv) /\
QSv + 131072 <= Qb + kPtrArrayResv /\ Qb + kPtrArrayResv <= ASAN_CEIL /\ (forall a, QR a <-> QSv <= a < QSv + 131072).
Proof. pose proof (SEED mb) as SEEDm. intros. pose proof Hinst_w as HinstW. eapply AGjt.QR_facts; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma ZQ_rstable_ : forall Wz, rstable (ZQ Wz).
Proof. pose proof (SEED mb) as SEEDm. intros. pose proof Hinst_w as HinstW. eapply AGjt.ZQ_rstable; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma ZQ_stableT_ : forall Wz, pstable WIN1T (ZQ Wz).
Proof. pose proof (SEED mb) as SEEDm. intros. pose proof Hinst_w as HinstW. eapply AGjt.ZQ_stableT; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma ZQ_stableD_ : forall Wz, pstable DX (ZQ Wz).
Proof. pose proof (SEED mb) as SEEDm. intros. pose proof Hinst_w as HinstW. eapply AGjt.ZQ_stableD; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma QSP_rstable_ : forall Wy, rstable (QSP Wy).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjo.QSP_rstable; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma rstable_and_ : forall R1 R2, rstable R1 -> rstable R2 -> rstable (fun m => R1 m /\ R2 m).
Proof. pose proof (SEED mb) as SEEDm. intros. eapply AGjl.rstable_and; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma pstable_and_ : forall (Xw : Z -> Prop) R1 R2, pstable Xw R1 -> pstable Xw R2 -> pstable Xw (fun m => R1 m /\ R2 m).
Proof. intros Xw R1 R2 A1 A2 m m' FR [H1 H2]. split; [exact (A1 m m' FR H1) | exact (A2 m m' FR H2)]. Qed.
Lemma segV_ : forall (Wy : world tfibsegs) (md1 : Model) (R : (word -> option byte) -> Prop), rstable R -> idx = res ->
forall c, at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZF Wy R)) S_VG Wy c ->
SRr tfibsegs Wy c (at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZ Wy R)) S_YJ).
Proof. pose proof (SEED mb) as SEEDm. intros. pose proof Hinst_w as HinstW. eapply AGjt.segV; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.
Lemma nodeV_ : forall {RT : Type} (Wy : world tfibsegs) (md1 : Model) (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfibsegs -> config -> Prop)
(R : (word -> option byte) -> Prop) (c1 : config),
idx = res ->
at_N Wy md1 WIN (PSR Wy SH2 R) S_V Wy c1 -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) ->
(forall m m' : word -> option byte, (forall x : word, ~ QR (bv_unsigned x) -> m' x = m x) -> R m -> R m') ->
amwf (cfg_model c1) ->
vm_reserved (m_vmmaps (cfg_model c1)) = segments_reserved tfibsegs ->
(forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
In (wiv (Qb, kPtrArrayResv)) (vm_maps (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wy) + 2 ^ 19 <= vm_limit (m_vmmaps (cfg_model c1)) ->
YM05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) z) ->
(forall (W5 : world tfibsegs) (c' : config), let md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) (cfg_model c1) in
wle Wy W5 -> hsub (w_H W5) (w_H Wy) -> (forall x : word, w_H Wy x = false -> w_H W5 x = false) ->
w_A W5 = (QSv, QSv + 131072) :: w_A Wy ->
(forall x : word, QSv <= bv_unsigned x < QSv + 131072 -> w_H W5 x = false) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H Wy x) ->
AI tfibsegs (w_H W5) (w_A W5) md5 -> amwf md5 -> same_io md0 md5 -> eager_used md5 <= eager_used (cfg_model c1) + 131072 ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps (cfg_model c1)) /\ vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps (cfg_model c1)) ->
at_S W5 md5 (fun a => WIN a \/ QR a) (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_VG W5 c' ->
amreal tfibsegs (K 1) W5 c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i))) /\
(forall i, aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) Wy (nx i) Q).
Proof. pose proof (SEED mb) as SEEDm. intros. pose proof Hinst_w as HinstW. eapply AGjt.nodeV; try eassumption. Unshelve. all: try exact DPOST; try exact S; try exact mem0; try exact md0; try exact 0%Z. Qed.

(* The tail of the grant arms ends in the machine post AGif4.sfin (the generic twin of AGjz.finE / finO: the depot's
   answer travels as [DPOST z memD]). *)
Definition finpost (Wz : world tfibsegs) (mdl : Model) (grow : bool) (z : Z) (W2 : world tfibsegs) (c2 : config) : Prop :=
W2 = Wz /\ exists regs' mem' matF,
c2 = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdl) matF mdl) /\
AGif4.sfin W ly regs0 mem0 inst n tr idx res mb DPOST grow z Wz regs' mem'.
Local Ltac run_byte HR x :=
rewrite <- (Z_to_bv_bv_unsigned 64 x); apply HR; cbn [fst snd].
Lemma fin_packG : forall (Wz : world tfibsegs) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z),
(grow = true <-> idx = res) -> (forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a) -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
forall (odd : bool) regs' mem' memD,
(odd = true <-> n mod 8 <> 0) ->
getr regs' 10 = sv_denot E0 (SOff aMAP 6144) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
(forall x : word, ~ X (bv_unsigned x) -> mem' x = mem0 x) ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H Wz) mem' a) ->
(forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wz) mem' a) ->
(forall a, SMv <= a < SMv + MSv / 8 -> (odd = true -> a <> PBv) -> apresent (w_H Wz) mem' a) ->
Forall (brun mem') (if odd then SH5o else SH5) ->
(bv_unsigned (getr regs0 15) <> 0 -> brun mem' (AGjm.Uv mb, AGjm.Uv mb + 4096, 190)) ->
DPOST z memD -> (forall a, DZONE a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a) -> (forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) ->
RX mem' -> FQ Wz grow mem' ->
(odd = true -> val_mem tfibsegs (mrestrict (w_H Wz) mem') PBv 1 (n mod 8) /\ apresent (w_H Wz) mem' PBv) ->
AGif4.sfin W ly regs0 mem0 inst n tr idx res mb DPOST grow z Wz regs' mem'.
Proof.
intros Wz X RX grow z Hgrow HXsub HRXQ odd regs' mem' memD Hodd R10 RCS MEQf PRSf HM HSH HRUN HFILL DP PRD EQD HRX FQm HPB.
pose proof INSTv_inst as EI.
destruct FQm as (Qslot & Qh0 & Qh8 & Qh16 & Qh24 & Qmag & Qbk & Qst & Qb1 & Qb2 & Qn & Qunw & Qres & Qnch & Qmtx & Qp1 & Qp2 & QPR & QVISW).
rewrite EI in Qres, Qnch, Qmtx, Qp1, Qp2.
assert (RUNS : brun mem' (SMv + 768, SMv + 768 + N8D / 8, 0) /\ brun mem' (SHBv + UEv / 8, SMv + MSv / 8, 250) /\
brun mem' (SMv + 512, SMv + 768, 250) /\ brun mem' (SMv, SMv + 512, 250)).
{ destruct odd; unfold AGjq.SH5o, AGjq.SH5 in HRUN;
apply Forall_cons_iff in HRUN as [R1 HRUN]; apply Forall_cons_iff in HRUN as [R2 HRUN];
apply Forall_cons_iff in HRUN as [R3 HRUN]; apply Forall_cons_iff in HRUN as [R4 _]; exact (conj R1 (conj R2 (conj R3 R4))). }
destruct RUNS as (Rzs & Rrt & Rhd & Rpg).
constructor; ims.
- exists memD. exact (conj DP (conj PRD EQD)).
- intros x N1 N2 N3. apply MEQf. intros HXx. destruct (HXsub _ HXx) as [Hw|[Hw|Hw]]; [exact (N1 Hw) | exact (N2 Hw) | exact (N3 Hw)].
- exact PRSf.
- intros a Ha. destruct (Z_lt_le_dec a (mb + 6144)) as [Hl|Hl]; [apply QPR; right; right; lia | apply HM; lia].
- intros a Ha. destruct odd.
+ destruct (Z.eq_dec a PBv) as [->|Hne]; [exact (proj2 (HPB eq_refl)) | apply HSH; [exact Ha | intros _; exact Hne]].
+ apply HSH; [exact Ha | intros E; discriminate E].
- intros Hg a Hqa. destruct (zr_dec QSv (QSv + 8) a) as [Hs|Hs]; [apply QPR; right; left; exact Hs|].
destruct (HRXQ Hg _ HRX (proj1 Hgrow Hg) a Hqa Hs) as [Hh Hm]. split; [exact Hh | eexists; exact Hm].
- intros a [Hw|Hs]; apply QPR; [left; exact Hw | right; left; exact Hs].
- exact QVISW.
- rewrite R10. cbn [sv_denot]. unfold aMAP. rewrite EaMAP. unfold YG0d.w64, YG0n.w64, AGjm.Uv. rewrite AGjm.Zbv_add_unsigned; first [reflexivity | f_equal; lia].
- exact RCS.
- intros x [Hx|Hx].
+ destruct (Z_lt_le_dec (bv_unsigned x) (SMv + 512)) as [Hl|Hl]; [run_byte Rpg x; lia | run_byte Rhd x; lia].
+ run_byte Rrt x; exact Hx.
- intros x Hx. run_byte Rzs x; exact Hx.
- intros H8. exact (proj1 (HPB (proj2 Hodd H8))).
- exact Qunw.
- exact Qres.
- exact Qnch.
- exact Qmtx.
- intros k Hk. cbn [ImgBase.im_segs AImg_A]. unfold aview.
assert (K : k = 1 \/ k = 2 \/ k = 3) by lia. destruct K as [->|[->| ->]].
+ pose proof (Qp1 0%nat ltac:(lia)) as Xb. rewrite Z.add_0_r in Xb. rewrite Xb. reflexivity.
+ pose proof (Qp2 0%nat ltac:(lia)) as Xb. rewrite Z.add_0_r in Xb. rewrite Xb. reflexivity.
+ pose proof (Qp2 1%nat ltac:(lia)) as Xb. replace (inst + o_sec_mutex + 3) with (inst + o_sec_mutex + 2 + Z.of_nat 1) by lia. rewrite Xb. reflexivity.
- exact Qslot.
- exact Qh0.
- exact Qh8.
- exact Qh16.
- exact Qh24.
- exact Qmag.
- exact Qbk.
- exact Qst.
- exact Qb1.
- exact Qb2.
- exact Qn.
- intros Hc x Hx. run_byte (HFILL Hc) x; exact Hx.
Qed.
Lemma finEG : forall (Wz : world tfibsegs) (mdl : Model) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z),
(grow = true <-> idx = res) -> (forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a) -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
n mod 8 = 0 -> forall W' c', at_S Wz mdl X (PSR Wz SH6 (PDX Wz RX z)) Ue_RET W' c' -> SRr tfibsegs W' c' (finpost Wz mdl grow z).
Proof.
intros Wz mdl X RX grow z Hgrow HXsub HRXQ H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (FQ Wz grow) Ue_RET) in HR; [| intros E1 ms1 HE1 HS1; eapply AGjz.FQ_e; eassumption].
eapply SRr_mono; [eapply (at_S_ret Wz mdl X _ Ue_RET _ _ (SOff aMAP 6144) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | repeat constructor] |].
intros W2 c2 _ (-> & regs' & mem' & matF & -> & R10 & RCS & MEQf & PRSf & (((HBf & HM & HSH & HRUN) & ((memD & DP & PRD & EQD) & HRX)) & FQm)).
unfold AGjq.SH6 in HRUN. apply Forall_cons_iff in HRUN as [Rf HRUN].
split; [reflexivity|]. exists regs', mem', matF. split; [reflexivity|].
apply (fin_packG Wz X RX grow z Hgrow HXsub HRXQ false regs' mem' memD); try assumption.
- split; [intros E; discriminate E | intros H; exfalso; exact (H H8)].
- intros a Ha _. exact (HSH a Ha).
- intros _. exact Rf.
- intros E; discriminate E.
Qed.
Lemma finOG : forall (Wz : world tfibsegs) (mdl : Model) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z),
(grow = true <-> idx = res) -> (forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a) -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
n mod 8 <> 0 -> forall W' c', at_S Wz mdl X (PT Wz SH6o (PDX Wz RX z)) Uo_RET W' c' -> SRr tfibsegs W' c' (finpost Wz mdl grow z).
Proof.
intros Wz mdl X RX grow z Hgrow HXsub HRXQ H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (fun m => FQ Wz grow m /\ val_mem tfibsegs (mrestrict (w_H Wz) m) PBv 1 (n mod 8) /\ apresent (w_H Wz) m PBv) Uo_RET) in HR;
[| intros E1 ms1 HE1 HS1; eapply AGjz.FQ_o; eassumption].
eapply SRr_mono; [eapply (at_S_ret Wz mdl X _ Uo_RET _ _ (SOff aMAP 6144) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | repeat constructor] |].
intros W2 c2 _ (-> & regs' & mem' & matF & -> & R10 & RCS & MEQf & PRSf & ((HBf & HM & HSH & HRUN & ((memD & DP & PRD & EQD) & HRX)) & (FQm & QPB & QPBp))).
unfold AGjq.SH6o in HRUN. apply Forall_cons_iff in HRUN as [Rf HRUN].
split; [reflexivity|]. exists regs', mem', matF. split; [reflexivity|].
apply (fin_packG Wz X RX grow z Hgrow HXsub HRXQ true regs' mem' memD); try assumption.
- split; [intros _; exact H8 | reflexivity].
- intros a Ha Hne. exact (HSH a Ha (Hne eq_refl)).
- intros _. exact Rf.
- intros _. exact (conj QPB QPBp).
Qed.
Lemma finEG0 : forall (Wz : world tfibsegs) (mdl : Model) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z),
(grow = true <-> idx = res) -> (forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a) -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
bv_unsigned (getr regs0 15) = 0 -> n mod 8 = 0 ->
forall W' c', at_S Wz mdl X (PSR Wz SH5 (PDX Wz RX z)) Ue_RET0 W' c' -> SRr tfibsegs W' c' (finpost Wz mdl grow z).
Proof.
intros Wz mdl X RX grow z Hgrow HXsub HRXQ C0 H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (FQ Wz grow) Ue_RET0) in HR; [| intros E1 ms1 HE1 HS1; eapply AGjz.FQ_e0; eassumption].
eapply SRr_mono; [eapply (at_S_ret Wz mdl X _ Ue_RET0 _ _ (SOff aMAP 6144) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | repeat constructor] |].
intros W2 c2 _ (-> & regs' & mem' & matF & -> & R10 & RCS & MEQf & PRSf & (((HBf & HM & HSH & HRUN) & ((memD & DP & PRD & EQD) & HRX)) & FQm)).
split; [reflexivity|]. exists regs', mem', matF. split; [reflexivity|].
apply (fin_packG Wz X RX grow z Hgrow HXsub HRXQ false regs' mem' memD); try assumption.
- split; [intros E; discriminate E | intros H; exfalso; exact (H H8)].
- intros a Ha _. exact (HSH a Ha).
- intros C. exfalso. exact (C C0).
- intros E; discriminate E.
Qed.
Lemma finOG0 : forall (Wz : world tfibsegs) (mdl : Model) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z),
(grow = true <-> idx = res) -> (forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a) -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
bv_unsigned (getr regs0 15) = 0 -> n mod 8 <> 0 ->
forall W' c', at_S Wz mdl X (PT Wz SH5o (PDX Wz RX z)) Uo_RET0 W' c' -> SRr tfibsegs W' c' (finpost Wz mdl grow z).
Proof.
intros Wz mdl X RX grow z Hgrow HXsub HRXQ C0 H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (fun m => FQ Wz grow m /\ val_mem tfibsegs (mrestrict (w_H Wz) m) PBv 1 (n mod 8) /\ apresent (w_H Wz) m PBv) Uo_RET0) in HR;
[| intros E1 ms1 HE1 HS1; eapply AGjz.FQ_o0; eassumption].
eapply SRr_mono; [eapply (at_S_ret Wz mdl X _ Uo_RET0 _ _ (SOff aMAP 6144) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | repeat constructor] |].
intros W2 c2 _ (-> & regs' & mem' & matF & -> & R10 & RCS & MEQf & PRSf & ((HBf & HM & HSH & HRUN & ((memD & DP & PRD & EQD) & HRX)) & (FQm & QPB & QPBp))).
split; [reflexivity|]. exists regs', mem', matF. split; [reflexivity|].
apply (fin_packG Wz X RX grow z Hgrow HXsub HRXQ true regs' mem' memD); try assumption.
- split; [intros _; exact H8 | reflexivity].
- intros a Ha Hne. exact (HSH a Ha (Hne eq_refl)).
- intros C. exfalso. exact (C C0).
- intros _. exact (conj QPB QPBp).
Qed.

(* The model's tail after the depot answer, and the leaf through ifs_post_grant. *)
Lemma NR : N8D / 8 < 18446744073709551615 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = false.
Proof.
intros Hsmall. pose proof (AGjy.sizes_model ly regs0 n tr res Htrlen Hinst Nrange S) as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. apply Z.leb_gt.
pose proof Nrange as NRs. clear - Hsmall NRs. unfold AGjm.N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hsmall by lia. lia.
Qed.
Lemma NRb : 18446744073709551615 <= N8D / 8 -> needs_remap (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) = true.
Proof.
intros Hbig. pose proof (AGjy.sizes_model ly regs0 n tr res Htrlen Hinst Nrange S) as (_ & _ & RS & _). unfold ck_n, needs_remap. cbn [YG00.ck_req]. rewrite RS. apply Z.leb_le.
pose proof Nrange as NRs. clear - Hbig NRs. unfold AGjm.N8D, kClearShadowMmapThreshold in *. rewrite Z.div_mul in Hbig by lia. lia.
Qed.
Lemma TAILg : N8D / 8 < 18446744073709551615 -> forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s4,
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
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hsmall grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub HSK HR D4 C4 SE4 A4 R4 RG4 N4 CI4 CA4 QT4 QG4 FS4 II4.
pose proof (AGjy.sizes_model ly regs0 n tr res Htrlen Hinst Nrange S) as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|]. cbn [amreal].
assert (LEAF : forall W' c', finpost Wz mdz grow z W' c' ->
QLEAF (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated), set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4) W' c').
{ intros W' c' (-> & regs' & mem' & matF & -> & HF).
pose proof HF as [Fdep _ FPRS _ _ _ _ _ FR10 FRCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
destruct Fdep as (memD & DP & _).
pose proof (AGif0n.if_dpost_aok _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W tr z memD DP) as AOK.
pose proof (AGif4.ifs_fresh _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 HARX) as FRESH.
assert (EQS : set_chunks (upd_chunk (st_chunks s4) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s4 = AGif4.SFSz S n tr z grow).
{ pose proof (AFib.upd_chunk_fresh (st_chunks S) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) FRESH) as UF.
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
Lemma TAILgB : 18446744073709551615 <= N8D / 8 -> forall (Wz : world tfibsegs) (c4 : config) (s4 : astate),
amreal tfibsegs (((z' <- askz (KShadowRemap (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated))
(8 * (ck_n (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated) / 8))) ;;
(if aGranted z' then YG00.ret tt else spin stag)) ;;
(YG00.modify (fun s0 => set_chunks (upd_chunk (st_chunks s0) (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)) s0) ;;
YG00.ret (ck_user (mkChunk (PSec (length (st_secs S1)) kPage) n CAllocated)))) s4) Wz c4 QLEAF.
Proof.
intros Hbig. exfalso. pose proof Nrange as NRs. clear - Hbig NRs. unfold AGjm.N8D in Hbig. unfold SEC_NMAX in NRs.
rewrite Z.div_mul in Hbig by (clear; lia).
pose proof (Z.div_lt_upper_bound n 8 (2 ^ 27) ltac:(clear; lia) ltac:(clear - NRs; lia)) as HH. clear NRs. lia.
Qed.
Lemma after_depot : forall (grow : bool) (Wz : world tfibsegs) (mdz : Model) (RX : (word -> option byte) -> Prop) (Xd : Z -> Prop) z c4 s3,
(grow = true <-> idx = res) -> rstable RX -> pstable WIN1T RX -> (grow = true -> forall m, RX m -> ZQ Wz m) ->
(forall a, WIN a -> Xd a) -> (forall a, Xd a -> WIN a \/ (grow = true /\ QR a) \/ DX a) ->
(forall matF, AGif4.skern grow W Wz md0 (with_vm_backing (m_vm_lazy mdz) matF mdz) ly mb MSv QSv) ->
at_S Wz mdz Xd (PSR Wz SH2 (PDX Wz RX z)) T_2 Wz c4 ->
st_depot s3 = st_depot S -> st_chunks s3 = st_chunks S -> st_secs s3 = st_secs S ++ [mkSec (sec_map_size n) (needed_size n) true] ->
st_sec_arr s3 = st_sec_arr S ++ [length (st_secs S)] ->
st_sec_reserved s3 = (if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S) -> st_regions s3 = st_regions S ->
st_nev s3 = st_nev S + 1 -> st_cache_inited s3 = st_cache_inited S -> st_cache s3 = st_cache S -> st_qthread s3 = st_qthread S ->
st_qglobal s3 = st_qglobal S -> st_fs s3 = st_fs S -> st_internal_inited s3 = st_internal_inited S ->
amreal tfibsegs (KDEP s3 (PSec (length (st_secs S1)) kPage) z) Wz c4 QLEAF.
Proof.
intros grow Wz mdz RX Xd z c4 s3 Hgrow RXs RXt HRXQ HXW HXsub HSK HR D3 C3 SE3 A3' R3 RG3 N3 CI3 CA3 QT3 QG3 FS3 II3.
unfold KDEP. destruct (Z_lt_le_dec (N8D / 8) 18446744073709551615) as [Hsm|Hbg].
- pose proof (fun s4 => TAILg Hsm grow Wz mdz RX Xd z c4 s4 Hgrow RXs RXt HRXQ HXW HXsub HSK HR) as TAIL.
rewrite (NR Hsm).
destruct (Z.eqb_spec z 0) as [Z0|Z0].
+ eapply amreal_pure; [reflexivity|]. apply TAIL; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_eq z 0) Z0). reflexivity.
+ cbn beta iota. rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (depot_ids _ + 1 <? kDepotIdsPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
unfold mcheck at 1. destruct (kStartFramesMax + _ + _ + 1 <? kStoreFramesPerBlock); [| cbn [amreal YG00.bind fail ibind]; exact I].
eapply amreal_pure; [reflexivity|]. eapply amreal_pure; [reflexivity|].
apply TAIL; cbn; try assumption. rewrite D3. unfold depot_after. rewrite (proj2 (Z.eqb_neq z 0) Z0). reflexivity.
- pose proof (fun s4 => TAILgB Hbg Wz c4 s4) as TAIL.
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

(* The arm where the pointer array still has a reserved slot. *)
Theorem grantS_ne : idx <> res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros NE. pose proof Hidx as HI. pose proof Hres as [HRS HRA].
pose proof (grant_cont_ W3 md2 (QSPX W3 (fun _ => True)) SUB3 VISM SHZ (conj (QSP3 NE) I)) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with false by (symmetry; apply Z.eqb_neq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact NE).
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
  - cbn [ImgBase.im_segs AImg_A]. rewrite A3. cbn [A_bytes fst snd]. zlia.
  - intros i Hi. cbn [ImgBase.im_segs AImg_A]. rewrite A3. cbn. right; right. exact Hi.
  - cbn [ImgBase.im_segs AImg_A]. rewrite A3. cbn. right; left. reflexivity.
  - cbn [ImgBase.im_segs AImg_A]. rewrite A3. cbn. left. reflexivity.
  - intros x N1 N2 _. exact (OUT3 x N1 N2). }
apply (after_depot false W3 md2 (fun _ => True) (fun a => WIN a \/ DX a) z c4 _ Hgrow RXs RXt HRXQ HXW' HXsub SK3 HR);
unfold S1; cbn; reflexivity.
Qed.

(* The arm where the pointer array is full: the kernel also commits its next page (AGjt.nodeV). *)
Theorem grantS_eq : idx = res -> amreal tfibsegs (KSEC 1) W3 ccont QLEAF.
Proof.
intros EQ. pose proof Hidx as HI. pose proof Hres as [HRS HRA]. pose proof (QR_facts_ EQ) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof (AGif4.ifs_ledger _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 HARX) as (LR & LSEG & LQ & LTOP).
pose proof (AGif4.ifs_room _ _ _ _ _ _ _ _ _ _ _ _ IFS inst ly S W mem0 md0 n HARX HRP) as ROOM. cbn [ImgBase.im_segs AImg_A] in ROOM.
pose proof (grant_cont_ W3 md2 (fun _ => True) SUB3 VISM SHZ I) as HR.
unfold KSEC. change (1 =? 0) with false. cbn iota. unfold sec_body. rewrite !bind_assoc_eq.
eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
eapply amreal_pure; [unfold mcheck; replace (Z.of_nat (length (st_sec_arr S1)) <? kMaxNumChunks) with true by (symmetry; apply Z.ltb_lt; unfold S1; cbn; rewrite <- Hidx_def; exact (proj2 HI)); reflexivity|].
rewrite !bind_assoc_eq. eapply amreal_pure; [reflexivity|]. rewrite !bind_assoc_eq.
replace (Z.of_nat (length (st_sec_arr S1)) =? st_sec_reserved S1) with true by (symmetry; apply Z.eqb_eq; unfold S1; cbn; rewrite <- Hidx_def, <- Hres_def; exact EQ).
rewrite !bind_assoc_eq. unfold YG00.bind at 1. unfold askz. cbn [ibind].
replace (8 * Z.of_nat (length (st_sec_arr S1))) with (8 * idx) by (unfold S1; cbn; rewrite <- Hidx_def; reflexivity).
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
apply (nodeV_ W3 md2 sV KV QLEAF (fun _ => True) c4 EQ HN HAI).
- clear; intros m m' _ _; exact I.
- rewrite EcM. exact MWV.
- rewrite EcM. unfold mdV. rewrite m_vmmaps_wvb, VMr. unfold mdN. rewrite m_vmmaps_wvb. exact LR.
- exact LSEG.
- rewrite EcM. unfold mdV. rewrite m_vmmaps_wvb, VMa. right. unfold mdN. rewrite m_vmmaps_wvb. exact LQ.
- rewrite EcM. unfold mdV. rewrite eager_used_wvb, m_vmmaps_wvb, VMl. unfold mdN in EG2 |- *. rewrite m_vmmaps_wvb. rewrite eager_used_wvb in EG2.
rewrite A3. cbn [A_bytes fst snd].
pose proof (IFR inst ly S W mem0 md0 n HARX HRP) as ROOMn. cbn [ImgBase.im_segs AImg_A] in ROOMn. pose proof MSBW_g as MSBW. pose proof MS8_g as MS8.
clear - ROOMn EG2 H3 Z9 MSBW MS8 HROOM. zlia.
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
  - cbn [ImgBase.im_segs AImg_A]. rewrite A5, A3. cbn [A_bytes fst snd]. zlia.
  - intros i Hi. cbn [ImgBase.im_segs AImg_A]. rewrite A5, A3. cbn. right; right; right. exact Hi.
  - cbn [ImgBase.im_segs AImg_A]. rewrite A5, A3. cbn. right; right; left. reflexivity.
  - cbn [ImgBase.im_segs AImg_A]. rewrite A5, A3. cbn. right; left. reflexivity.
  - intros x N1 N2 N3. cbn [ImgBase.im_segs AImg_A]. rewrite (OUT5 x (fun H => N3 (conj eq_refl H))). exact (OUT3 x N1 N2). }
apply (after_depot true W5 md5 (RZ W5 (fun _ => True)) (fun a => (WIN a \/ QR a) \/ DX a) z c6 _ Hgrow RS5 RT5 HRXQ HXW' HXsub SK5 HR);
unfold S1; cbn; try reflexivity.
- rewrite EcM. exact (same_io_wvb md2 matV IO2).
Qed.
End h.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The secondary arms from Allocate's entry: the prefix to the mmap ecall at mb := 0, the node, and the arms at the
   granted base.  The leaf is AGif4.alloc_leaf0 over regs0, without the model path (in this unit only [sec_arms] below uses this lemma; AGioM.alloc_sec_w_em adds the path over the memnorm twin's leaf, AGioM.v:196-198). *)
Lemma sec_arms_w :
amreal tfibsegs ((ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t stag n tr ob) (set_nev (st_nev S + 1) S)) W
(cfg_at tfibsegs A_Allocate regsU mem0 md0)
(AGif4.alloc_leaf0 B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n).
Proof using B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS NMAXW NOBW ROOMW IFA IFG IFR HNOB HROOM TS inst ly S W regs0 mem0 md0 n tr
idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp Hgp Hra Hra4096 Hcf Hsp Htrlen Hso Hbp
Hinst Nrange HnW Hnmax Hidx Hres Hidx_def Hres_def Hpres0 PBUF0 SV HARX HRP Htr Hlive regsU SEED.
change (set_nev (st_nev S + 1) S) with S1. change (AGif4.alloc_leaf0 B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n) with QLEAF.
rewrite sec_ask_eq. cbn [amreal].
pose proof (@AGjh.seg0 _ W ly regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 Hpres0 (m_vm_materialized md0) regsU (SEED 0) PBUF0) as PFX.
unfold cfg_at. replace md0 with (with_vm_backing (m_vm_lazy md0) (m_vm_materialized md0) md0) at 1 by (apply with_vm_backing_id).
eapply SRr_bind; [exact PFX|]. clear PFX. intros W1 c1 _ HR1. pose proof (proj1 HR1) as EW. subst W1.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (@AGji.seg1 _ _ W ly regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 LY IMG Hn Hsp Htrlen Hbp Hinst Nrange Hidx Hres _ _ HR1))|].
clear HR1 c1. intros W1 c1 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W1.
pose proof HN as HNc. destruct HNc as (_ & ms1 & mat1 & E1 & Ec1 & _).
assert (EcM : cfg_model c1 = with_vm_backing (m_vm_lazy md0) mat1 md0) by (rewrite Ec1; reflexivity).
apply (node_sec 0 S1 KSEC QLEAF c1 HN HAI).
- intros z Hz. exact Hz.
- intros c' HRf. rewrite EcM in HRf. exact (refuseS 0 mat1 c' HRf).
- intros a W3 ms E'. cbv zeta. rewrite EcM.
intros GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 AI2 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB.
set (A := bv_unsigned a) in *.
assert (EA : a = w64 A) by (unfold w64, A; symmetry; apply Z_to_bv_bv_unsigned).
rewrite EA in GOK, AI2, MW2, IO2, EG2, VM2. rewrite EA.
pose proof (AGjm.size_facts n Nrange) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _).
(* the map is at most n + 3 pages: inside the bound up to which grants stay apart (ifs_apart_w) *)
assert (MSBW : 0 < AGjm.MSv n <= NMAXW + 4 * 4096) by (clear - Z3 Z7 Z8 Z10 HnW; lia).
pose proof (AFia.grant_parts _ (w64 A) _ GOK) as (GP1 & _).
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
+ eapply (grantS_eq A); eassumption.
+ eapply (grantS_ne A); eassumption.
- rewrite EcM. apply YG0b.same_io_with_vm_backing.
Qed.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The secondary arms at the cgif model's bound MALLOC_MAX: sec_arms_w at NMAXW := MALLOC_MAX, where ifs_apart_w is
   AIfaceS's own ifs_apart.  The section repeats Section f's declarations at that bound, so the statement is the
   unwidened one (no lemma in this unit uses it; AGioM.alloc_sec_em, AGioM.v:259, goes through alloc_sec_w_em). *)
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
Hypothesis Hinst : 0xa1000 <= INSTv /\ INSTv + 0xe60 <= 0x12d120 /\ INSTv mod 8 = 0.
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
Lemma sec_arms :
amreal tfibsegs ((ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t stag n tr ob) (set_nev (st_nev S + 1) S)) W
(cfg_at tfibsegs A_Allocate regsU mem0 md0)
(AGif4.alloc_leaf0 B ARX AOX lpost TFIB_OOM inst ly S W regs0 mem0 md0 n).
Proof using B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS TS inst ly S W regs0 mem0 md0 n tr
idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp Hgp Hra Hra4096 Hcf Hsp Htrlen Hso Hbp
Hinst Nrange Hnmax Hidx Hres Hidx_def Hres_def Hpres0 PBUF0 SV HARX HRP Htr Hlive regsU SEED.
exact (sec_arms_w B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF IFS MALLOC_MAX ImgBaseAGS.NOB (2 ^ 30)
  (AGif4.ifs_apart _ _ _ _ _ _ _ _ _ _ _ _ IFS) (AGif4.ifs_grant _ _ _ _ _ _ _ _ _ _ _ _ IFS)
  (AGif4.ifs_room _ _ _ _ _ _ _ _ _ _ _ _ IFS)
  ltac:(unfold MALLOC_MAX, ImgBaseAGS.NOB, YF06.NOB; lia) ltac:(unfold MALLOC_MAX; vm_compute; discriminate) TS inst ly S W regs0 mem0 md0 n tr
  idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 LY IMG HTSD Hn Hi11 Htp Hgp Hra Hra4096 Hcf Hsp Htrlen Hso Hbp
  Hinst (AGi9.nrange_sec n Nrange) (proj2 Nrange) Hnmax Hidx Hres Hidx_def Hres_def Hpres0 PBUF0 SV HARX HRP Htr Hlive regsU SEED).
Qed.
End fc.
End d.
