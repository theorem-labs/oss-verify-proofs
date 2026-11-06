(* The free half of the any-U allocator: the free sub-contracts in ARU form and the helpers only the free walks share. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The sub-contracts that free's walks call (lib/A/AFeu.v drain_body, do_recycle, cache_dealloc, recycle_chunk;
   lib/A/AFew.v enqueue; lib/A/AFfs.v recycle_chunk of a secondary chunk). Each U form is the donor text read through
   ARU: the pre is the donor pre of FSupoison.unpoison U mem plus FSupoison.upoison_ok / upoisoned; the leaf is the donor
   leaf with acall_post replaced by FSupoisonU.acall_postU and every other memory clause read on unpoison U mem / mem'.
   Each U leaf ends with the raw frame: DIfaceR.acall_raw_x at the leaf's stack constant and E, read on the raw
   memories mem / mem' themselves (route 1's ARU lift); the walks build it from their runs' frames (raw_of_meq). *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFK.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m YF0x YFl1 YFeu YFew.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Section fk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. A configuration determines its registers, memory and model.                                                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma cfg_at_inj : forall pc pc' regs regs' (m m' : word -> option byte) md md',
  cfg_at tfibsegs pc regs m md = cfg_at tfibsegs pc' regs' m' md' -> regs = regs' /\ m = m' /\ md = md'.
Proof. intros pc pc' regs regs' m m' md md' E. unfold cfg_at, YK11.mkst in E. injection E as E1 E2 E3 E4. auto. Qed.

Section c.
Variable B : asyms.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The sub-contracts of free in ARU form (lib/B/YFeu.v:191-284, lib/B/YFew.v:26-56, lib/B/YFfs.v:24-27).        *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Definition drain_preU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  drain_pre B ly X W regs (FSP.unpoison U mem) md /\ FSP.upoison_ok B ly X U /\ FSP.upoisoned tfibsegs W mem U.
Definition drain_leafU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B DSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B DSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_drain_specU : Prop :=
  forall ly X U W regs mem md,
    drain_preU ly X U W regs mem md ->
    amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) (drain_leafU ly X U W regs mem md).

Definition dr_preU (ly : alayout) (X : astate) (P : list batch) (U : list (Z * Z)) (W : world tfibsegs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  dr_pre B ly X P W regs (FSP.unpoison U mem) md /\ FSP.upoison_ok B ly X U /\ FSP.upoisoned tfibsegs W mem U.
Definition dr_leafU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B DRSTACK ly X U W regs mem md (fun a => spZ regs <= a < spZ regs + 32) ly (snd r) W' regs' mem' md' /\
    (forall a, spZ regs <= a < spZ regs + 32 -> apresent (w_H W') (FSP.unpoison U mem') a) /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B DRSTACK regs (bv_unsigned x) -> ~ (spZ regs <= bv_unsigned x < spZ regs + 32) -> mem' x = mem x).
Definition tfib_dorecycle_specU : Prop :=
  forall ly X P U W regs mem md,
    dr_preU ly X P U W regs mem md ->
    amreal tfibsegs (do_recycle 100000%nat P X) W (cfg_at tfibsegs A_DoRecycle regs mem md) (dr_leafU ly X U W regs mem md).

Definition cd_preU (ly : alayout) (X : astate) (c off : Z) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  cd_pre B ly X c off W regs (FSP.unpoison U mem) md /\ FSP.upoison_ok B ly X U /\ FSP.upoisoned tfibsegs W mem U.
Definition cd_leafU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B KSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    (forall a, 0 <= a < 2 ^ 64 -> puser ly X a ->
       aview tfibsegs (w_H W') (FSP.unpoison U mem') a = aview tfibsegs (w_H W) (FSP.unpoison U mem) a) /\
    st_cache_inited (snd r) = true /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_cdealloc_specU : Prop :=
  forall ly X c off U W regs mem md,
    cd_preU ly X c off U W regs mem md ->
    amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (cd_leafU ly X U W regs mem md).

Definition rcc_preU (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (U : list (Z * Z)) (W : world tfibsegs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  rcc_pre B ly X k cbp W regs (FSP.unpoison U mem) md /\ FSP.upoison_ok B ly X U /\ FSP.upoisoned tfibsegs W mem U.
Definition rcc_leafU (ly : alayout) (X : astate) (k : chunk) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B KSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    (forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
       aview tfibsegs (w_H W') (FSP.unpoison U mem') a = aview tfibsegs (w_H W) (FSP.unpoison U mem) a) /\
    st_cache_inited (snd r) = true /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_rchunk_specU : Prop :=
  forall ly X k cbp U W regs mem md,
    rcc_preU ly X k cbp U W regs mem md ->
    amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafU ly X k U W regs mem md).
(* lib/B/YFfs.v:24 tfib_rchunk_sec_spec, any U. *)
Definition tfib_rchunk_sec_specU : Prop :=
  forall ly X k cbp U W regs mem md r o,
    rcc_preU ly X k cbp U W regs mem md -> ck_beg k = PSec r o ->
    amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafU ly X k U W regs mem md).

Definition enq_preU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (k : chunk) : Prop :=
  enq_pre B ly X W regs (FSP.unpoison U mem) md k /\ FSP.upoison_ok B ly X U /\ FSP.upoisoned tfibsegs W mem U.
Definition enq_leafU (ly : alayout) (X : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (k : chunk) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md' nb,
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B QSTACK ly X U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    st_qthread (snd r) = qc_push (st_qthread X) k nb /\
    match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
    st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
    st_fs (snd r) = st_fs X /\
    (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ ascratch B QSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x).
Definition tfib_enqueue_spec_nbU (nbq : bool) : Prop :=
  forall ly X U W regs mem md k,
    need_new_batch (st_qthread X) = nbq ->
    enq_preU ly X U W regs mem md k ->
    amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leafU ly X U W regs mem md k).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. From the donor leaf proved on the unpoisoned reading (the donor's leaf lemma applied at unpoison U mem, for   *)
(*    the configuration whose memory is unpoison U mem') plus U's two invariants, to the U leaf.                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma drain_leafU_intro : forall ly X U W regs mem md r W' regs' mem' md',
  drain_leaf B ly X W regs (FSP.unpoison U mem) md r W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison U mem') md') ->
  FSP.upoison_ok B ly (snd r) U -> FSP.upoisoned tfibsegs W' mem' U ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
     ~ ascratch B DSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x) ->
  drain_leafU ly X U W regs mem md r W' (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
intros ly X U W regs mem md r W' regs' mem' md' (r2 & m2 & d2 & E & P) OK PO RAW.
apply cfg_at_inj in E as (<- & <- & <-). exists regs', mem', md'. split; [reflexivity|]. exact (conj (conj P (conj OK PO)) RAW).
Qed.
Lemma dr_leafU_intro : forall ly X U W regs mem md r W' regs' mem' md',
  dr_leaf B ly X W regs (FSP.unpoison U mem) md r W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison U mem') md') ->
  FSP.upoison_ok B ly (snd r) U -> FSP.upoisoned tfibsegs W' mem' U ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
     ~ ascratch B DRSTACK regs (bv_unsigned x) -> ~ (spZ regs <= bv_unsigned x < spZ regs + 32) -> mem' x = mem x) ->
  dr_leafU ly X U W regs mem md r W' (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
intros ly X U W regs mem md r W' regs' mem' md' (r2 & m2 & d2 & E & P & PR) OK PO RAW.
apply cfg_at_inj in E as (<- & <- & <-). exists regs', mem', md'. split; [reflexivity|]. exact (conj (conj P (conj OK PO)) (conj PR RAW)).
Qed.
Lemma cd_leafU_intro : forall ly X U W regs mem md r W' regs' mem' md',
  cd_leaf B ly X W regs (FSP.unpoison U mem) md r W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison U mem') md') ->
  FSP.upoison_ok B ly (snd r) U -> FSP.upoisoned tfibsegs W' mem' U ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
     ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x) ->
  cd_leafU ly X U W regs mem md r W' (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
intros ly X U W regs mem md r W' regs' mem' md' (r2 & m2 & d2 & E & P & FR & CI) OK PO RAW.
apply cfg_at_inj in E as (<- & <- & <-). exists regs', mem', md'. split; [reflexivity|]. exact (conj (conj P (conj OK PO)) (conj FR (conj CI RAW))).
Qed.
Lemma rcc_leafU_intro : forall ly X k U W regs mem md r W' regs' mem' md',
  rcc_leaf B ly X k W regs (FSP.unpoison U mem) md r W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison U mem') md') ->
  FSP.upoison_ok B ly (snd r) U -> FSP.upoisoned tfibsegs W' mem' U ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
     ~ ascratch B KSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x) ->
  rcc_leafU ly X k U W regs mem md r W' (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
intros ly X k U W regs mem md r W' regs' mem' md' (r2 & m2 & d2 & E & P & FR & CI) OK PO RAW.
apply cfg_at_inj in E as (<- & <- & <-). exists regs', mem', md'. split; [reflexivity|]. exact (conj (conj P (conj OK PO)) (conj FR (conj CI RAW))).
Qed.
Lemma enq_leafU_intro : forall ly X U W regs mem md k r W' regs' mem' md',
  enq_leaf B ly X W regs (FSP.unpoison U mem) md k r W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison U mem') md') ->
  FSP.upoison_ok B ly (snd r) U -> FSP.upoisoned tfibsegs W' mem' U ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
     ~ ascratch B QSTACK regs (bv_unsigned x) -> ~ False -> mem' x = mem x) ->
  enq_leafU ly X U W regs mem md k r W' (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
intros ly X U W regs mem md k r W' regs' mem' md' (r2 & m2 & d2 & nb & E & P & Q) OK PO RAW.
apply cfg_at_inj in E as (<- & <- & <-). exists regs', mem', md', nb. split; [reflexivity|].
destruct Q as (Q1 & Q2 & Q3 & Q4 & Q5). exact (conj (conj P (conj OK PO)) (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 RAW)))))).
Qed.
(* The U leaf of free (FSupoisonU.free_leafU) from the donor free_leaf on the unpoisoned reading. *)
Lemma free_leafU_intro : forall ly S U W regs mem md p n r W' regs' mem' md',
  free_leaf tfibsegs B ly S W regs (FSP.unpoison U mem) md p n r W' (cfg_at tfibsegs (raZ regs) regs' (FSP.unpoison U mem') md') ->
  (forall ly', layout_le (length (st_secs S)) ly ly' -> FSP.upoison_ok B ly' (snd r) U) -> FSP.upoisoned tfibsegs W' mem' U ->
  FSU.free_leafU tfibsegs B ly S U W regs mem md p n r W' (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
intros ly S U W regs mem md p n r W' regs' mem' md' (ly2 & r2 & m2 & d2 & E & P & QT) OK PO.
apply cfg_at_inj in E as (<- & <- & <-). exists ly2, regs', mem', md'. split; [reflexivity|].
split; [|exact QT]. refine (conj P (conj (OK ly2 (proj1 (proj2 P))) PO)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. Where U is not, for the free walks: the shadow of the image (the globals' shadow cells of Tfib_const,          *)
(*    lib/B/YF0m.v:240) is off U, since no live block meets the image (AR_client_img_law, YG0d.v).                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma offU_img_shadow : forall ly S U W mem md g, FSP.ARU tfibsegs B ly S U W mem md ->
  TFIB_IMG_LO <= g < TFIB_IMG_END -> FAR.offU U (shadow_addr g).
Proof.
intros ly S U W mem md g H Hg.
pose proof (FSP.ARU_AR tfibsegs B ly S U W mem md H) as HAR.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as [IC1 IC2].
apply (FAR.offU_shadow_nonlive B ly S U W mem md g H); [unfold TFIB_IMG_LO, TFIB_IMG_END in Hg; lia|].
intros p n Hb Hin.
destruct (al_client_img _ _ LAWS ly S W (FSP.unpoison U mem) md g HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hb Hin))))) as [NZ _].
apply NZ. unfold in_zr. lia.
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. free of a block (pa, n) with every UP range outside it (FSupoisonU.afree_realizesU's premise): its shadow     *)
(*    holds no UP byte, and UP stays in the live blocks that remain.                                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section f.
Variable B : asyms.
Lemma ush_out_block_shadow : forall ly S UP pa len s, 0 < len -> FSP.upoison_ok B ly S UP ->
  (forall r, In r UP -> fst r + snd r <= pa \/ pa + len <= fst r) ->
  FSP.in_ush UP s = true -> ~ (SHADOW_OFF + pa / 8 <= s <= SHADOW_OFF + (pa + len - 1) / 8).
Proof.
intros ly S UP pa len s Hl [F _] OUT Hs [S1 S2]. rewrite Forall_forall in F.
apply FSP.in_ush_spec in Hs as (r & Hr & H1 & H2). destruct (F r Hr) as (A8 & L8 & M8 & _).
apply Z.mod_divide in A8 as [a Ha]; [|lia]. apply Z.mod_divide in M8 as [b Hb]; [|lia].
unfold shadow_addr in H1, H2. rewrite Ha in H1, H2. rewrite Hb in H2. rewrite !Z.div_mul in H1, H2 by lia.
pose proof (Z.div_mod pa 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound pa 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (pa + len - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (pa + len - 1) 8 ltac:(lia)) as M2.
assert (Ea : a * 8 / 8 = a) by (apply Z.div_mul; lia). assert (Eb : b * 8 / 8 = b) by (apply Z.div_mul; lia).
rewrite ?Ea, ?Eb in H1, H2.
destruct (OUT r Hr) as [O|O].
- assert (E1 : a + b <= pa / 8) by (apply Z.div_le_lower_bound; lia). lia.
- assert (E2 : (pa + len - 1) / 8 < a) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma upoison_ok_free : forall ly S ly' S' UP pa n, FSP.upoison_ok B ly S UP ->
  (forall r, In r UP -> fst r + snd r <= pa \/ pa + req_size n <= fst r) ->
  (forall q m, In (q, m) (ablocks B ly S) -> (q, m) <> (pa, n) -> In (q, m) (ablocks B ly' S')) ->
  FSP.upoison_ok B ly' S' UP.
Proof.
intros ly S ly' S' UP pa n OK OUT KEEP. apply (FAR.upoison_ok_keep B ly S ly' S' UP OK).
intros r q m Hr Hb H1 H2. apply KEEP; [exact Hb|]. intros E. injection E as -> ->.
destruct OK as [F _]. rewrite Forall_forall in F. destruct (F r Hr) as (_ & L8 & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)). destruct (OUT r Hr); lia.
Qed.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. Two steps every free walk takes (proposed by a Theorem Labs sub-lane): a zone3 range is application memory, so off UP;  *)
(*    a run whose write window misses the shadow band keeps UP's 0xf7 bytes.                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section z.
Variable B : asyms.
Variables (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (mem : word -> option byte) (md : Model).
Hypothesis HARU : FSP.ARU tfibsegs B ly S UP W mem md.
Lemma offU_zone3 : forall x sz a, zone3 x sz -> x <= a < x + sz -> FAR.offU UP a.
Proof.
intros x sz a (Z1 & Z2 & Z3) Ha. pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
apply (FAR.offU_app B ly S UP W mem md a HARU); [lia|].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma upoisoned_frame : forall (mem' : word -> option byte) (WINp : Z -> Prop),
  (forall a, WINp a -> ~ (kLowShadowBeg <= a < kHighMemBeg)) ->
  (forall x : word, ~ WINp (bv_unsigned x) -> mem' x = mem x) ->
  FSP.upoisoned tfibsegs W mem' UP.
Proof.
intros mem' WINp WZ FR. apply (FAR.upoisoned_keep UP W W mem mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem md HARU)).
intros s Hs. pose proof (FSP.ush_facts tfibsegs B ly S UP W mem md s HARU Hs) as (_ & L1 & L2).
apply FSP.aview_at. apply FR. rewrite FSP.wz by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
intros Hw. apply (WZ s Hw). unfold kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
End z.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 7. The raw frame of a U leaf (its last conjunct, DIfaceR.acall_raw_x's text) from a run's frame on the raw       *)
(*    memory: every byte of the run's write window is owned (before or after), scratch, or in E.                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma raw_of_meq : forall (WIN OX OX' SC E : Z -> Prop) (mem mem' : word -> option byte),
  (forall x : word, ~ WIN (bv_unsigned x) -> mem' x = mem x) ->
  (forall a, 0 <= a < 2 ^ 64 -> WIN a -> OX a \/ OX' a \/ SC a \/ E a) ->
  forall x : word, ~ OX (bv_unsigned x) -> ~ OX' (bv_unsigned x) -> ~ SC (bv_unsigned x) -> ~ E (bv_unsigned x) ->
  mem' x = mem x.
Proof.
intros WIN OX OX' SC E mem mem' MQ INC x N1 N2 N3 N4. apply MQ. intros Hw.
destruct (INC _ (bv_unsigned_in_range _ x) Hw) as [H|[H|[H|H]]]; contradiction.
Qed.
End fk.
