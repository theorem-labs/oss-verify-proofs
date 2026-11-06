(* Image-neutral companion of the frozen shared text (RtPFShared.v): nothing here names an image, so every unit
   relocates it once.
   - ff_stable64: ff_stable with the memory change asked only at 64-bit addresses (a reader reads Z_to_bv 64 a, so at an
     address outside [0, 2^64) it aliases a 64-bit one and the frozen premise cannot be shown when the window changes);
   - sh_apcommon_realizesUz: printf_common with the argument slots disjoint from its window (a v* caller knows only
     that its va area misses its window) and below 2^47 (the Bz walk reads a cleaned store that drops higher bytes);
   - sh_asnprintf_monoU / sh_asnprintf_mono: the snprintf window K is a lower bound (U and AR forms);
   - srr_fx_continue: the continuation through the FP-existential post;
   - sh_avsnprintf_realizesUa / sh_avsnprintf_icpt_realizesUa / sh_avfprintf_icpt_realizesUx: the GXA-route
     intermediate forms of the v* contracts (extra premises a caller in the chain gives);
   - dest_off_globals_of_ablocks / _of_stack / _of_fake: dest_off_globals by measurement;
   - va_slots_below_47 (+ _AR, _nil): the snprintf top's slot bound from the caller's own frame;
   - amem8_of_high / amem8_of_stack (+ amem_range_le): the top's destination slack by measurement.
   New file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFupoison.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtPFPf RtPFShared.
Import ListNotations.
Local Open Scope Z_scope.

Definition ff_stable64 (FF : fmt_fam) : Prop :=
forall (rd rd' : reader) rs f ws T, FF rd rs f ws T ->
(forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a \/ (Exists (in_zr a) rs /\ ~ (SHADOW_OFF <= a < kHighMemBeg))) ->
FF rd' rs f ws T.
Lemma ff_stable_of_64 : forall FF, ff_stable64 FF -> ff_stable FF.
Proof. intros FF H rd rd' rs f ws T HF HK. apply (H rd rd' rs f ws T HF). intros a _. exact (HK a). Qed.

(* ---- intervals (image-neutral) ---- *)
Lemma zdisjoint_sub : forall x r r', zdisjoint x r -> fst r <= fst r' -> fst r' + snd r' <= fst r + snd r ->
  zdisjoint x r'.
Proof. intros [x1 x2] [r1 r2] [s1 s2]. unfold zdisjoint. cbn [fst snd]. lia. Qed.
Lemma Forall_snp : forall (P : Z * Z -> Prop) K sp d w, Forall P (snp_out K sp d w) <-> P (sp - K, K) /\ P (d, w).
Proof.
intros P K sp d w. unfold snp_out. split.
- intros HF. inversion HF as [|? ? H1 HF2]; subst. inversion HF2; subst. split; assumption.
- intros [H1 H2]. constructor; [exact H1 | constructor; [exact H2 | constructor]].
Qed.
Lemma pairwise_snp : forall K sp d w, pairwise zdisjoint (snp_out K sp d w) <-> zdisjoint (sp - K, K) (d, w).
Proof.
intros K sp d w. unfold snp_out. cbn [pairwise]. split.
- intros (H1 & _ & _). inversion H1; subst. assumption.
- intros H. split; [constructor; [exact H | constructor]|]. split; [constructor | exact I].
Qed.
(* ---- the snprintf window is a LOWER bound: a contract at K1 gives it at every K2 >= K1 ---- *)
(* a larger window's premises give the smaller window's (its regions shrink; ff_mono for the FF clause), and the
   smaller window's post (fewer bytes may change) gives the larger one's *)
Lemma snp_out_shrink : forall x K1 K2 sp d w, K1 <= K2 ->
  Forall (zdisjoint x) (snp_out K2 sp d w) -> Forall (zdisjoint x) (snp_out K1 sp d w).
Proof.
intros x K1 K2 sp d w HK Hx. apply Forall_snp in Hx as [X1 X2]. apply Forall_snp. split; [|exact X2].
apply (zdisjoint_sub x (sp - K2, K2)); [exact X1 | cbn [fst snd]; lia | cbn [fst snd]; lia].
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Definition sh_apcommon_realizesUz (FF : fmt_fam) (K : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md f ap (ws T : list Z),
ecall_preU segs B ly S U W regs mem md -> ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (zdisjoint (spZ regs - K, K)) cr ->
words_at (aview segs (w_H W) mem) ap ws -> zdisjoint (ap, 8 * Z.of_nat (length ws)) (spZ regs - K, K) ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
FF (aview segs (w_H W) mem) [(spZ regs - K, K)] f ws T ->
SRr segs W (cfg_at segs pc regs mem md) (fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\ ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\
same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- the continuation lemma for the FP-existential post ---- *)
(* A caller binds the callee's returned FP state fx' and continues at @cfg_at fx' (its own remaining segments are proved
   Context {fx}, and ARU / aregs_preserved / the memory post never mention fx), reaching its own goal Q. REST is the rest
   of the callee's post (ARU, a0, bytes, frame, apresent), independent of the ambient fx. One apply per call site; disco,
   boxreg and this port set their context record's FP field to fx' and discharge the continuation. *)
Lemma srr_fx_continue : forall (W : world segs) (c : config) (ra : Z)
  (REST : YK11.FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world segs -> config -> Prop),
  SRr segs W c
    (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
       c' = @cfg_at fx' segs ra regs' mem' md' /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
       Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
       REST fx' regs' mem' md') ->
  (forall (fx' : YK11.FPState) regs' mem' md',
     (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) ->
     Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 ->
     REST fx' regs' mem' md' ->
     SRr segs W (@cfg_at fx' segs ra regs' mem' md') Q) ->
  SRr segs W c Q.
Proof.
intros W c ra REST Q H1 H2. eapply SRr_bind; [exact H1|].
intros W' c' Hle (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HR). exact (H2 fx' regs' mem' md' Hf1 Hf2 HR).
Qed.

(* ---- dest_off_globals discharge: heap block above the image, or a stack frame above the image ---- *)
Lemma dest_off_globals_of_ablocks : forall ly S (b sz d w img_lo img_hi : Z),
  In (b, sz) (ablocks B ly S) -> img_hi <= b -> b <= d ->
  zdisjoint (d, w) (img_lo, img_hi - img_lo).
Proof. intros ly S b sz d w img_lo img_hi _ Hb Hd. unfold zdisjoint. cbn [fst snd]. right. lia. Qed.
Lemma dest_off_globals_of_stack : forall ly (d w img_lo img_hi : Z),
  img_hi <= ly_stk_lo ly -> ly_stk_lo ly <= d ->
  zdisjoint (d, w) (img_lo, img_hi - img_lo).
Proof. intros ly d w img_lo img_hi Hs Hd. unfold zdisjoint. cbn [fst snd]. right. lia. Qed.
(* a local destination in an ASan fake frame (__asan_stack_malloc_N): parametric in the fake-stack region's base fs_lo,
   so each unit plugs its own stack_malloc contract's range fact *)
Lemma dest_off_globals_of_fake : forall (fs_lo d w img_lo img_hi : Z),
  img_hi <= fs_lo -> fs_lo <= d ->
  zdisjoint (d, w) (img_lo, img_hi - img_lo).
Proof. intros fs_lo d w img_lo img_hi Hf Hd. unfold zdisjoint. cbn [fst snd]. right. lia. Qed.
(* ---- the GXA-route intermediate forms (fm's chain proves these; the top derives their extra premises) ---- *)
(* the vsnprintf entries with three premises every caller in the chain can give: the argument slots at or above the
   entry sp, the destination off them, and below 2^47 *)
Definition sh_avsnprintf_realizesUa (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md d n f ap (ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* order: the arguments lie at or above the entry sp (every caller's va area is its own spill or above it) *)
spZ regs <= ap ->
(* the destination is below the window or above the argument slots (GXA VfprintfCall.v:42, first disjunction) *)
(d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d) ->
(* the argument slots below 2^47 (the normalized store GXA and printf_common's cleaned run read drops higher bytes) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* the destination's slack word: GXA's range check pf_rng asks app_mem (D + i + 7) for each written byte *)
amem_range d (sn_len (n - 1) T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition sh_avsnprintf_icpt_realizesUa (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md d n f ap (ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* order: the arguments lie at or above the entry sp (every caller's va area is its own spill or above it) *)
spZ regs <= ap ->
(* the destination is below the window or above the argument slots (GXA VfprintfCall.v:42, first disjunction) *)
(d + sn_len (n - 1) T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= d) ->
(* the argument slots below 2^47 (the normalized store GXA and printf_common's cleaned run read drops higher bytes) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* the destination's slack word: GXA's range check pf_rng asks app_mem (D + i + 7) for each written byte *)
amem_range d (sn_len (n - 1) T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* the vfprintf interceptor / musl vfprintf with GXA's four premises (fuzz_manifest's text, from its
   lib/A/FMgxaSeamDef.v, verbatim; this file is its one definition) *)
Definition sh_avfprintf_icpt_realizesUx
    (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md fp f ap bp cp s0 n0 (ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
words_at (aview segs (w_H W) mem) fp (sn_file snw bp cp) -> 0 < bp ->
words_at (aview segs (w_H W) mem) cp [s0; n0] ->
dest_ok segs B ly S W regs mem fp 232 -> dest_ok segs B ly S W regs mem cp 16 ->
0 <= fp -> fp + 232 <= 2 ^ 63 -> 0 <= cp -> cp + 16 <= 2 ^ 63 ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
Forall (zdisjoint (gv, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
FF (aview segs (w_H W) mem) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) f ws T ->
0 <= n0 < 2 ^ 31 - 1 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < s0 -> s0 + sn_len n0 T <= 2 ^ 63 ->
pairwise zdisjoint (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
dest_ok segs B ly S W regs mem s0 (sn_len n0 T) -> amem_range s0 (sn_len n0 T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF s0 (sn_len n0 T) ->
shadow_hull_vis (aview segs (w_H W) mem) s0 (sn_len n0 T) ->
zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* GXA (1): musl vsnprintf's `*c.s = 0`, the only NUL an empty output leaves *)
aview segs (w_H W) mem s0 = Some 0 ->
(* GXA (2): the frame order musl vsnprintf builds *)
spZ regs <= fp -> fp + 232 <= cp -> cp + 16 <= ap ->
(* GXA (3): the destination is below the window or above the caller's slots *)
(s0 + sn_len n0 T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= s0) ->
(* GXA (4): the FILE, the cookie and the slots are user memory (with GXA (2), all below 2^47) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* GXA (5): the destination's slack word (pf_rng, AsanFacts.v:78-80: app_mem (D + i + 7) for each written byte) *)
amem_range s0 (sn_len n0 T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len n0 T -> aview segs (w_H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
~ Exists (in_zr a) [(spZ regs - K, K); (fp, 232); (cp, 16)] -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* the AR form (no user-poisoned range) of the Ux contract, and the U = [] instance, as RtPFShared's sh_*_of_U *)
Definition sh_avfprintf_icpt_realizesx
    (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (snw pc : Z) : Prop :=
forall ly S W regs mem md fp f ap bp cp s0 n0 (ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 fp -> getr regs 11 = w64 f -> getr regs 12 = w64 ap ->
words_at (aview segs (w_H W) mem) fp (sn_file snw bp cp) -> 0 < bp ->
words_at (aview segs (w_H W) mem) cp [s0; n0] ->
dest_ok segs B ly S W regs mem fp 232 -> dest_ok segs B ly S W regs mem cp 16 ->
0 <= fp -> fp + 232 <= 2 ^ 63 -> 0 <= cp -> cp + 16 <= 2 ^ 63 ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
Forall (zdisjoint (gv, 8)) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
words_at (aview segs (w_H W) mem) ap ws ->
0 <= ap -> ap + 8 * Z.of_nat (length ws) < 2 ^ 63 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
FF (aview segs (w_H W) mem) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) f ws T ->
0 <= n0 < 2 ^ 31 - 1 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < s0 -> s0 + sn_len n0 T <= 2 ^ 63 ->
pairwise zdisjoint (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp) ->
dest_ok segs B ly S W regs mem s0 (sn_len n0 T) -> amem_range s0 (sn_len n0 T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF s0 (sn_len n0 T) ->
shadow_hull_vis (aview segs (w_H W) mem) s0 (sn_len n0 T) ->
zdisjoint (s0, sn_len n0 T) (img_lo, img_hi - img_lo) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* GXA (1): musl vsnprintf's `*c.s = 0`, the only NUL an empty output leaves *)
aview segs (w_H W) mem s0 = Some 0 ->
(* GXA (2): the frame order musl vsnprintf builds *)
spZ regs <= fp -> fp + 232 <= cp -> cp + 16 <= ap ->
(* GXA (3): the destination is below the window or above the caller's slots *)
(s0 + sn_len n0 T <= spZ regs - K \/ ap + 8 * Z.of_nat (length ws) <= s0) ->
(* GXA (4): the FILE, the cookie and the slots are user memory (with GXA (2), all below 2^47) *)
ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
(* GXA (5): the destination's slack word (pf_rng, AsanFacts.v:78-80: app_mem (D + i + 7) for each written byte) *)
amem_range s0 (sn_len n0 T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len n0 T -> aview segs (w_H W) mem' (s0 + i) = Some (nth (Z.to_nat i) (sn_bytes n0 T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + sn_len n0 T) ->
~ Exists (in_zr a) [(spZ regs - K, K); (fp, 232); (cp, 16)] -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Lemma sh_avfprintf_icpt_of_Ux : forall FF K gc gv img_lo img_hi cr snw pc,
  sh_avfprintf_icpt_realizesUx FF K gc gv img_lo img_hi cr snw pc ->
  sh_avfprintf_icpt_realizesx FF K gc gv img_lo img_hi cr snw pc.
Proof.
intros FF K gc gv img_lo img_hi cr snw pc HU ly S W regs mem md fp f ap bp cp s0 n0 ws T cval Hpre. intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md fp f ap bp cp s0 n0 ws T cval); try eassumption.
  apply ecall_preU_nil. exact Hpre.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|].
  exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.

(* ---- a callee proved for a weaker family (and fewer read-only ranges) serves a caller with a stronger one ---- *)
Lemma sh_apcommon_realizesUz_weaken : forall FF1 FF2 K cr1 cr2 pc,
  (forall rd rs f ws T, FF2 rd rs f ws T -> FF1 rd rs f ws T) ->
  (forall r1, In r1 cr1 -> exists r2, In r2 cr2 /\ fst r2 <= fst r1 /\ fst r1 + snd r1 <= fst r2 + snd r2) ->
  sh_apcommon_realizesUz FF1 K cr1 pc -> sh_apcommon_realizesUz FF2 K cr2 pc.
Proof.
intros FF1 FF2 K cr1 cr2 pc Hsub Hcr H1 ly S U W regs mem md f ap ws T Hpre Hlo Hp R11 R12 Hcv Hcb Hcd Hws Hapd Hap0
  Hap47 HFF.
apply (H1 ly S U W regs mem md f ap ws T Hpre Hlo Hp R11 R12); try assumption.
- intros a Ha. apply Hcv. rewrite Exists_exists in Ha |- *. destruct Ha as (r1 & Hr1 & Hin).
  destruct (Hcr r1 Hr1) as (r2 & Hr2 & L1 & L2). exists r2. split; [exact Hr2|]. unfold in_zr in *. lia.
- rewrite Forall_forall in Hcb |- *. intros r1 Hr1. destruct (Hcr r1 Hr1) as (r2 & Hr2 & L1 & L2).
  pose proof (Hcb r2 Hr2). lia.
- rewrite Forall_forall in Hcd |- *. intros r1 Hr1. destruct (Hcr r1 Hr1) as (r2 & Hr2 & L1 & L2).
  exact (zdisjoint_sub _ r2 r1 (Hcd r2 Hr2) L1 L2).
- apply Hsub. exact HFF.
Qed.
Lemma sh_avfprintf_icpt_realizesUx_ff : forall FF1 FF2 K gc gv img_lo img_hi cr snw pc,
  (forall rd rs f ws T, FF2 rd rs f ws T -> FF1 rd rs f ws T) ->
  sh_avfprintf_icpt_realizesUx FF1 K gc gv img_lo img_hi cr snw pc ->
  sh_avfprintf_icpt_realizesUx FF2 K gc gv img_lo img_hi cr snw pc.
Proof.
intros FF1 FF2 K gc gv img_lo img_hi cr snw pc Hsub H1. unfold sh_avfprintf_icpt_realizesUx in *. intros.
eapply H1; eauto.
Qed.

(* ---- the snprintf top's argument-slot bound (spZ regs + 8 |xs| <= 2^47) from the caller's own frame ---- *)
(* a caller's outgoing argument slots lie on its stack, below ly_stk_hi ly <= kHighMemEnd = 2^47 *)
Lemma va_slots_below_47 : forall ly S U W regs mem md (xs : list Z),
  ecall_preU segs B ly S U W regs mem md ->
  spZ regs + 8 * Z.of_nat (length xs) <= ly_stk_hi ly ->
  spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47.
Proof.
intros ly S U W regs mem md xs ((HAR & _) & _ & _) Hx.
pose proof (stk_kHighMemBeg B ly S _ (proj1 HAR)) as [_ Ht]. unfold kHighMemEnd in Ht. lia.
Qed.
Lemma va_slots_below_47_AR : forall ly S W regs mem md (xs : list Z),
  ecall_pre segs B ly S W regs mem md ->
  spZ regs + 8 * Z.of_nat (length xs) <= ly_stk_hi ly ->
  spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47.
Proof.
intros ly S W regs mem md xs H Hx. apply (va_slots_below_47 ly S [] W regs mem md xs); [|exact Hx].
apply ecall_preU_nil. exact H.
Qed.
(* no stack slots (every argument in a3..a7): the bound is free *)
Lemma va_slots_below_47_nil : forall ly S U W regs mem md,
  ecall_preU segs B ly S U W regs mem md -> spZ regs + 8 * Z.of_nat (length (@nil Z)) <= 2 ^ 47.
Proof.
intros ly S U W regs mem md H. apply (va_slots_below_47 ly S U W regs mem md []); [exact H|].
destruct H as ((_ & _ & _ & _ & Hhi & _) & _ & _). cbn [length]. lia.
Qed.

(* ---- the snprintf top's destination slack (amem_range d (w + 8)) by measurement ---- *)
Lemma amem_range_le : forall p n m, n <= m -> amem_range p m -> amem_range p n.
Proof. intros p n m Hnm H. unfold amem_range in *. lia. Qed.
(* a destination in high application memory below the allocation ceiling (every heap block) *)
Lemma amem8_of_high : forall d w, kHighMemBeg <= d -> d + w + 8 <= alloc_ceiling -> amem_range d (w + 8).
Proof.
intros d w H1 H2. pose proof alloc_ceiling_val as C. unfold amem_range, kHighMemEnd. lia.
Qed.
(* a destination on the stack at least 9 bytes below the stack's top *)
Lemma amem8_of_stack : forall ly S U W regs mem md d w,
  ecall_preU segs B ly S U W regs mem md -> kHighMemBeg <= d -> d + w + 9 <= ly_stk_hi ly -> amem_range d (w + 8).
Proof.
intros ly S U W regs mem md d w ((HAR & _) & _ & _) H1 H2.
pose proof (stk_kHighMemBeg B ly S _ (proj1 HAR)) as [_ Ht]. unfold amem_range. lia.
Qed.

(* the U form and the AR form of the K lower bound *)
Lemma sh_asnprintf_monoU : forall FF K1 K2 gc gv img_lo img_hi cr pc,
  ff_mono FF -> K1 <= K2 ->
  sh_asnprintf_realizesU segs B FF K1 gc gv img_lo img_hi cr pc ->
  sh_asnprintf_realizesU segs B FF K2 gc gv img_lo img_hi cr pc.
Proof.
intros FF K1 K2 gc gv img_lo img_hi cr pc MONO HK H1
  ly S U W regs mem md d n f xs ws T cval Hpre Hlo Hp R10 R11 R12 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hva Hxs Hxsd
  HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm.
set (w := sn_len (n - 1) T) in *.
eapply SRr_mono.
- apply (H1 ly S U W regs mem md d n f xs ws T cval Hpre); try assumption.
  + lia.
  + intros a Ha. apply Hp. lia.
  + rewrite Forall_forall in Hcd |- *. intros r Hr. exact (snp_out_shrink r K1 K2 _ _ _ HK (Hcd r Hr)).
  + exact (snp_out_shrink _ K1 K2 _ _ _ HK Hgcd).
  + exact (snp_out_shrink _ K1 K2 _ _ _ HK Hgvd).
  + exact (snp_out_shrink _ K1 K2 _ _ _ HK Hxsd).
  + apply (MONO _ (snp_out K2 (spZ regs) d w)); [exact HFF|].
    intros r' Hr'. unfold snp_out in Hr'. destruct Hr' as [<-|[<-|[]]].
    * exists (spZ regs - K2, K2). split; [left; reflexivity | cbn [fst snd]; lia].
    * exists (d, w). split; [right; left; reflexivity | cbn [fst snd]; lia].
  + apply pairwise_snp in Hpw. apply pairwise_snp. unfold zdisjoint in *. cbn [fst snd] in *. lia.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & Hap & Hsb & H10 & Hby & Hfr & Hpm).
  split; [reflexivity|]. exists fx', regs', mem', md'. split; [reflexivity|].
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HA|]. split; [exact Hap|]. split; [exact Hsb|].
  split; [exact H10|]. split; [exact Hby|]. split; [|exact Hpm].
  intros a Ha H2 H3. apply Hfr; [exact Ha | exact H2 | lia].
Qed.
Lemma sh_asnprintf_mono : forall FF K1 K2 gc gv img_lo img_hi cr pc,
  ff_mono FF -> K1 <= K2 ->
  sh_asnprintf_realizes segs B FF K1 gc gv img_lo img_hi cr pc ->
  sh_asnprintf_realizes segs B FF K2 gc gv img_lo img_hi cr pc.
Proof.
intros FF K1 K2 gc gv img_lo img_hi cr pc MONO HK H1
  ly S W regs mem md d n f xs ws T cval Hpre Hlo Hp R10 R11 R12 Hcv Hcb Hcd Hgc Hgv G1 G2 G3 G4 Hgcd Hgvd Hva Hxs Hxsd
  HFF Hn HT Hd0 Hdw Hpw Hdst Ham Hra Hhull Hdog Hfrm.
set (w := sn_len (n - 1) T) in *.
eapply SRr_mono.
- apply (H1 ly S W regs mem md d n f xs ws T cval Hpre); try assumption.
  + lia.
  + intros a Ha. apply Hp. lia.
  + rewrite Forall_forall in Hcd |- *. intros r Hr. exact (snp_out_shrink r K1 K2 _ _ _ HK (Hcd r Hr)).
  + exact (snp_out_shrink _ K1 K2 _ _ _ HK Hgcd).
  + exact (snp_out_shrink _ K1 K2 _ _ _ HK Hgvd).
  + exact (snp_out_shrink _ K1 K2 _ _ _ HK Hxsd).
  + apply (MONO _ (snp_out K2 (spZ regs) d w)); [exact HFF|].
    intros r' Hr'. unfold snp_out in Hr'. destruct Hr' as [<-|[<-|[]]].
    * exists (spZ regs - K2, K2). split; [left; reflexivity | cbn [fst snd]; lia].
    * exists (d, w). split; [right; left; reflexivity | cbn [fst snd]; lia].
  + apply pairwise_snp in Hpw. apply pairwise_snp. unfold zdisjoint in *. cbn [fst snd] in *. lia.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & Hap & Hsb & H10 & Hby & Hfr & Hpm).
  split; [reflexivity|]. exists fx', regs', mem', md'. split; [reflexivity|].
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HA|]. split; [exact Hap|]. split; [exact Hsb|].
  split; [exact H10|]. split; [exact Hby|]. split; [|exact Hpm].
  intros a Ha H2 H3. apply Hfr; [exact Ha | exact H2 | lia].
Qed.
End s.
