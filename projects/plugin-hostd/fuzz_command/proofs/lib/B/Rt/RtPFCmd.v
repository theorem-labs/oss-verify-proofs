(* plugin-hostd/fuzz_command's snprintf and sprintf contracts in the shared shape of
   omx-clap-core/fuzz_manifest's FMsnprintfShared.v, which this tree carries unchanged
   except module paths as RtPFShared.v, with RtPFPf.v (FMsnprintfPf.v), RtPFupoison.v (FMupoison.v) and RtPFSx.v
   (FMsnprintfSx.v: sh_asnprintf_mono(U), the GXA-route forms
   sh_avsnprintf_realizesUa / sh_avsnprintf_icpt_realizesUa / sh_avfprintf_icpt_realizesUx, sh_apcommon_realizesUz with
   its 2^47 slot bound, and the measurement helpers va_slots_below_47 / amem8_of_high / amem8_of_stack).
   - FR_cmd: the format family of fuzz_command's printf language (lib/Prog/printf_facts_c.v:10-89: literal bytes,
     %d %c %04x %02x %llu %s %.*s), as the shared contracts take their family parameter; pf_parse_cmd / pf_text_cmd
     say that RtPFPf's parser and renderer are printf_facts_c's on every piece. Since 2026-10-29 it has the shape of
     fuzz_manifest's FF_fm (lib/A/FMsnprintfFmI.v:31-36), the family the
     GXA route is proved for: the format is a nonempty literal of the image below the GOT word CMD_GOTW (GXA reads it
     as image data, lib/CJ/RL/GXA/G_vfprintf_snf.v:210), and each string argument has its slack word and 8 bytes past
     its NUL in application memory (cmd_args_slack / cmd_args_amem, local copies of the route's pf_args_slack and
     pf_args_amem). On image A every snprintf / sprintf call of fuzz_command passes a .rodata literal and no string
     argument (measured at image A's call sites); the same program code is measured on this image at its call sites.
   - asnprintf_sh: our snprintf text cmd_asnprintf_realizes at FR_cmd, with the window CMD_SNP_K, the image range
     0x10000 .. 0x606000 for dest_off_globals, and the read-only list CMD_SNP_CR, whose body is CMD_CR's: every
     read-only byte of the image (its two non-writable segments), as the route's seam asks (ro_covered, fuzz_manifest's
     FMgxaSeam.v:345). cmd_asnprintf_realizes is the shared sh_asnprintf_realizes (the U = [] form, RtPFShared.v)
     with one premise changed: consts_view over cr becomes RtDefs.rt_rom_view, the UNOWNED read-only bytes (a call
     site carries no AR for the runtime-owned ones; a proof gets those from AR, RtPFCv.v).
   - sh_asprintf_realizes(U): the sprintf text in the same shape, with no size (the ASan wrapper reaches musl's
     vsnprintf with n = 0x7fffffff, so the whole text and its terminator are written) and the same rt_rom_view
     premise; asprintf_sh is it at FR_cmd with the window CMD_SP_K and the list CMD_SP_CR (CMD_CR's body too). Since
     2026-10-29 it carries the two premises the GXA-route vsnprintf interceptor
     (sh_avsnprintf_icpt_realizesUa) needs from its caller, in the snprintf top's shape: the caller's argument slots
     below 2^47 and the destination's slack word (amem_range d (sp_len T + 8)).
   - dest_off_globals for a destination in an ASan fake frame of S: RtPFDog.v (it needs the image's segments, which
     this file does not, so RtFormat.v can import this file alone).
   The entry addresses on the pinned image (nm, objdump): snprintf 0x451d0, sprintf 0x451cc (the interceptor
   trampolines); the stack-protector cells musl vfprintf reads, the GOT word 0xa6bf8 (ld s2 at 0x9aeec) and
   __stack_chk_guard 0x604158.
   The windows (prologue addi sp of each function on the path, objdump): snprintf 0x451d0 -> ___interceptor_snprintf
   96 -> ___interceptor_vsnprintf 2,160 -> musl vsnprintf 304 -> ___interceptor_vfprintf 48 -> musl vfprintf, so the
   glue to musl vfprintf's entry is 2,608 (0xa30, fm's number too), and with GXA's VF_DEPTH 5,552 below that entry
   the route needs 8,160 <= 2 * ESTACK; printf_common (frame 2,240) is entered at 2,256 and 2,608. sprintf 0x451cc ->
   ___interceptor_sprintf 80 -> ___interceptor_vsprintf 2,160 -> musl vsprintf 0 (tail jump to the vsnprintf
   trampoline) -> ___interceptor_vsnprintf 2,160 -> musl vsnprintf 304 -> ___interceptor_vfprintf 48: glue 4,752,
   route 10,304 <= 3 * ESTACK. sh_asnprintf_mono lifts a window to any larger one. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/RtPFCmd.v for fuzz_command.asan-ubsan: module paths and that image's addresses (the two entry PCs, the stack-guard cells, the image hull and the image's read-only segments CMD_CR). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require printf_facts_c.
Import ListNotations.
Local Open Scope Z_scope.

Module PF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.printf_facts_c.

(* ---- fuzz_command's constants ---- *)
Definition CMD_IMG_LO : Z := 0x10000.
Definition CMD_IMG_HI : Z := 0x606000.
Definition CMD_SNPRINTF_PC : Z := 0x451d0.
Definition CMD_SPRINTF_PC : Z := 0x451cc.
Definition CMD_GOTW : Z := 0xa6bf8.
Definition CMD_GUARD : Z := 0x604158.
(* the windows at the two entries (header: glue + GXA's VF_DEPTH, 8,160 and 10,304) *)
Definition CMD_SNP_K : Z := 2 * ESTACK.
Definition CMD_SP_K : Z := 3 * ESTACK.

(* ---- the family ---- *)
(* fuzz_command's conversions: every piece of its pf_parse *)
Definition pf_cmd_piece (p : pf_piece) : Prop :=
match p with PLit _ | Pd | Pc | Px04 | Px02 | Pllu | Ps | Pps => True end.
(* the slack word after each string argument, and 8 bytes past its NUL, lie in application memory: fuzz_manifest's
   FMgxaSeamDef.pf_args_slack and RT_pf_sh.pf_args_amem, copied so that this statement file needs no
   route module *)
Fixpoint cmd_args_slack (ws : list Z) (args : list pf_arg) : Prop :=
  match args, ws with
  | [], _ => True
  | APtr s :: args', w :: ws' => amem_range w (str_end w s - w) /\ cmd_args_slack ws' args'
  | _ :: args', _ :: ws' => cmd_args_slack ws' args'
  | _ :: _, [] => False
  end.
Fixpoint cmd_args_amem (ws : list Z) (args : list pf_arg) : Prop :=
  match args, ws with
  | APtr s :: a', w :: w' => amem_range w (Z.of_nat (length s) + 8) /\ cmd_args_amem w' a'
  | _ :: a', _ :: w' => cmd_args_amem w' a'
  | _, _ => True
  end.
(* fuzz_command's family in the shape of fuzz_manifest's FF_fm (FMsnprintfFmI.v:31-36): our pieces, the format a
   nonempty literal of the image below the GOT word, and the two argument facts *)
Definition FR_cmd : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall pf_cmd_piece ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    CMD_IMG_LO <= f /\ f + Z.of_nat (length fmt) + 1 <= CMD_GOTW /\ cmd_args_slack ws args /\
    fmt <> [] /\ cmd_args_amem ws args.
(* what a call site checks by computation for the five facts: the format a nonempty literal below the GOT word,
   and no string argument (then the two argument facts hold with nothing to show) *)
Definition fr_lit_ok (f : Z) (fmt : list Z) (args : list pf_arg) : bool :=
  (CMD_IMG_LO <=? f) && (f + Z.of_nat (length fmt) + 1 <=? CMD_GOTW) &&
  match fmt with [] => false | _ :: _ => true end &&
  forallb (fun a => match a with APtr _ => false | _ => true end) args.

Lemma pf_cmd_piece_all : forall ps, Forall pf_cmd_piece ps.
Proof. intros ps. induction ps as [|p ps IH]; constructor; [destruct p; exact I | exact IH]. Qed.

(* printf_facts_c's pieces and arguments as RtPFPf's *)
Definition piece_of (p : PF.pf_piece) : pf_piece :=
match p with
| PF.PLit b => PLit b | PF.Pd => Pd | PF.Pc => Pc | PF.Px04 => Px04 | PF.Px02 => Px02
| PF.Pllu => Pllu | PF.Ps => Ps | PF.Pps => Pps
end.
Definition arg_of (a : PF.pf_arg) : pf_arg :=
match a with PF.AInt v => AInt v | PF.AU64 u => AU64 u | PF.APtr s => APtr s end.

Lemma pf_parse_cmd : forall f, pf_parse f = option_map (map piece_of) (PF.pf_parse f).
Proof.
fix IH 1. intros f. destruct f as [|b r]; [reflexivity|].
cbn [pf_parse PF.pf_parse].
destruct (b =? 37).
- destruct r as [|c r1]; [reflexivity|]. cbn beta iota.
  destruct (c =? 100); [rewrite (IH r1); destruct (PF.pf_parse r1); reflexivity|].
  destruct (c =? 99); [rewrite (IH r1); destruct (PF.pf_parse r1); reflexivity|].
  destruct (c =? 115); [rewrite (IH r1); destruct (PF.pf_parse r1); reflexivity|].
  destruct (c =? 48).
  + destruct r1 as [|c2 [|c3 r3]]; [reflexivity | reflexivity |]. cbn beta iota.
    destruct ((c2 =? 52) && (c3 =? 120)); [rewrite (IH r3); destruct (PF.pf_parse r3); reflexivity|].
    destruct ((c2 =? 50) && (c3 =? 120)); [rewrite (IH r3); destruct (PF.pf_parse r3); reflexivity | reflexivity].
  + destruct (c =? 108).
    * destruct r1 as [|c2 [|c3 r3]]; [reflexivity | reflexivity |]. cbn beta iota.
      destruct ((c2 =? 108) && (c3 =? 117)); [rewrite (IH r3); destruct (PF.pf_parse r3); reflexivity | reflexivity].
    * destruct (c =? 46); [|reflexivity].
      destruct r1 as [|c2 [|c3 r3]]; [reflexivity | reflexivity |]. cbn beta iota.
      destruct ((c2 =? 42) && (c3 =? 115)); [rewrite (IH r3); destruct (PF.pf_parse r3); reflexivity | reflexivity].
- destruct ((0 <? b) && (b <? 256)); [rewrite (IH r); destruct (PF.pf_parse r); reflexivity | reflexivity].
Qed.

Lemma pf_text_cmd : forall ps args, pf_text (map piece_of ps) (map arg_of args) = PF.pf_text ps args.
Proof.
intros ps. induction ps as [|p ps IH]; intros args.
- destruct args; reflexivity.
- destruct p; cbn [map piece_of pf_text PF.pf_text].
  + rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map arg_of]; try reflexivity. rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map arg_of]; try reflexivity. rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map arg_of]; try reflexivity. rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map arg_of]; try reflexivity. rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map arg_of]; try reflexivity. rewrite IH. reflexivity.
  + destruct args as [|[v|u|s] args]; cbn [map arg_of]; try reflexivity. rewrite IH. reflexivity.
  + destruct args as [|[k|u|s] [|[v2|u2|s2] args]]; cbn [map arg_of]; try reflexivity.
    destruct ((0 <=? k) && (k <=? Z.of_nat (length s2))); [|reflexivity]. rewrite IH. reflexivity.
Qed.

(* the family from fuzz_command's own parse and text, with the boolean check of the format and the arguments *)
Lemma FR_cmd_intro : forall rd rs f ws T fmt ps args,
  fmt_at rd rs f fmt -> PF.pf_parse fmt = Some ps -> pf_args_asan rd rs ws (map arg_of args) ->
  PF.pf_text ps args = Some T -> pf_prec_pos (map piece_of ps) (map arg_of args) ->
  fr_lit_ok f fmt (map arg_of args) = true ->
  FR_cmd rd rs f ws T.
Proof.
intros rd rs f ws T fmt ps args Hf Hp Ha Ht Hpos Hok.
unfold fr_lit_ok in Hok. repeat rewrite andb_true_iff in Hok. destruct Hok as (((Hlo & Hhi) & Hne) & Hstr).
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
assert (Hne' : fmt <> []) by (destruct fmt; [discriminate Hne | discriminate]).
assert (SA : forall ws0 args0, pf_args_asan rd rs ws0 args0 ->
  forallb (fun a => match a with APtr _ => false | _ => true end) args0 = true ->
  cmd_args_slack ws0 args0 /\ cmd_args_amem ws0 args0).
{ intros ws0 args0. revert ws0. induction args0 as [|a args0 IH]; intros ws0 Ha0 Hs0.
  - destruct ws0; split; exact I.
  - destruct ws0 as [|w ws0]; [exact (False_ind _ Ha0)|]. destruct Ha0 as [_ Ha0].
    cbn [forallb] in Hs0. apply andb_true_iff in Hs0 as [Hs1 Hs0].
    destruct (IH ws0 Ha0 Hs0) as [S M].
    destruct a as [v|u|s]; [exact (conj S M) | exact (conj S M) | discriminate Hs1]. }
destruct (SA ws (map arg_of args) Ha Hstr) as [Hsl Ham].
exists fmt, (map piece_of ps), (map arg_of args).
split; [exact Hf|]. split; [rewrite pf_parse_cmd, Hp; reflexivity|].
split; [apply pf_cmd_piece_all|]. split; [exact Ha|]. split; [rewrite pf_text_cmd; exact Ht|].
exact (conj Hpos (conj Hlo (conj Hhi (conj Hsl (conj Hne' Ham))))).
Qed.

(* Every read-only byte of the image the proofs run on: the non-writable segments of its loaded image (tfibsegs,
   lib/B/YB1v.v = images.AsanUbsan's loaded_segments: the R-- and R-X PT_LOADs of fuzz_command.asan-ubsan bbe55d24
   rounded out to whole pages, [0x10000, 0x33000) and [0x33000, 0xa5000); lib/B/Rt/RtPFCv.v cmd_cr_segs pins it by
   computation), the list the GXA route's seam asks of a contract (ro_covered, FMgxaSeam.v:345 of fuzz_manifest, whose
   fm_cr, FMsnprintfCr.v:22, is the same expression). The lists of the two contracts, CMD_SNP_CR and CMD_SP_CR, have
   the same literal body (each is CMD_CR by reflexivity), so a call site's premise unfolds to the two ranges; before
   2026-10-29 they were the word lists each chain named. *)
Definition CMD_CR : list (Z * Z) := [(0x10000, 0x23000); (0x33000, 0x72000)].
Definition CMD_SNP_CR : list (Z * Z) := [(0x10000, 0x23000); (0x33000, 0x72000)].
Definition CMD_SP_CR : list (Z * Z) := [(0x10000, 0x23000); (0x33000, 0x72000)].

Definition in_cmd_img (r : Z * Z) : bool :=
(CMD_IMG_LO <=? fst r) && (0 <=? snd r) && (fst r + snd r <=? CMD_IMG_HI).
Lemma cmd_snp_cr_img : forallb in_cmd_img CMD_SNP_CR = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cmd_sp_cr_img : forallb in_cmd_img CMD_SP_CR = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- sprintf's text in the shared shape ---- *)
(* the arguments start at a2 *)
Definition va_words2 (regs : bvmap 5 word) (rd : reader) (sp : Z) (xs ws : list Z) : Prop :=
ws = map (argZ regs) [2; 3; 4; 5; 6; 7] ++ xs /\ words_at rd sp xs.
(* the whole text and its terminator *)
Definition sp_bytes (T : list Z) : list Z := T ++ [0].
Definition sp_len (T : list Z) : Z := Z.of_nat (length T) + 1.
(* at musl's vsnprintf with n = 0x7fffffff, the shared written part and bytes are these *)
Lemma sp_len_sn : forall T, Z.of_nat (length T) < 2 ^ 31 - 1 -> sn_len (0x7fffffff - 1) T = sp_len T.
Proof.
intros T HT. unfold sn_len, sn_bytes, sp_len. rewrite length_app, firstn_all2 by lia. cbn [length]. lia.
Qed.
Lemma sp_bytes_sn : forall T, Z.of_nat (length T) < 2 ^ 31 - 1 -> sn_bytes (0x7fffffff - 1) T = sp_bytes T.
Proof. intros T HT. unfold sn_bytes, sp_bytes. rewrite firstn_all2 by lia. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* ---- sprintf (d, f, ...), entered with a stack window of K bytes ---- *)
Definition sh_asprintf_realizesU (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S (U : list (Z * Z)) W regs mem md d f (xs ws T : list Z) cval,
ecall_preU segs B ly S U W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 f ->
RtDefs.rt_rom_view segs B W mem -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sp_len T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sp_len T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sp_len T)) ->
va_words2 regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) < 2 ^ 63 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sp_len T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sp_len T)) f ws T ->
Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sp_len T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sp_len T)) ->
dest_ok segs B ly S W regs mem d (sp_len T) -> amem_range d (sp_len T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sp_len T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sp_len T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sp_len T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* the argument slots below 2^47 (the vsnprintf interceptor's GXA-route premise) *) spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
(* the destination's slack word (GXA's range check asks app_mem (D + i + 7)) *) amem_range d (sp_len T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARU segs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sp_len T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sp_bytes T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sp_len T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* no user-poisoned range *)
Definition sh_asprintf_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d f (xs ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 f ->
RtDefs.rt_rom_view segs B W mem -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sp_len T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sp_len T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sp_len T)) ->
va_words2 regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) < 2 ^ 63 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sp_len T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sp_len T)) f ws T ->
Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sp_len T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sp_len T)) ->
dest_ok segs B ly S W regs mem d (sp_len T) -> amem_range d (sp_len T) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sp_len T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sp_len T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sp_len T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(* the argument slots below 2^47 (the vsnprintf interceptor's GXA-route premise) *) spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
(* the destination's slack word (GXA's range check asks app_mem (D + i + 7)) *) amem_range d (sp_len T + 8) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sp_len T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sp_bytes T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sp_len T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Lemma sh_asprintf_of_U : forall FF K gc gv img_lo img_hi cr pc,
  sh_asprintf_realizesU FF K gc gv img_lo img_hi cr pc -> sh_asprintf_realizes FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc HU ly S W regs mem md d f xs ws T cval Hpre. intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md d f xs ws T cval); try eassumption.
  apply ecall_preU_nil. exact Hpre.
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|]. exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.

(* ---- snprintf in our text: fuzz_manifest's shared sh_asnprintf_realizes (RtPFShared.v) with ONE premise changed ----
   The shared text asks consts_view over cr; with cr the whole read-only image that covers the runtime-owned
   read-only bytes too, whose values come only from AR, which a call site does not carry. Our text asks instead the
   unowned half, RtDefs.rt_rom_view (the premise the string contracts take), and keeps every other line of the shared
   text verbatim; cmd_asnprintf_of_sh carries the shared text to ours given that rt_rom_view and the state give
   consts_view over cr (for this image: RtPFCv.cmd_cr_consts_view, the owned half from AR). *)
Definition cmd_asnprintf_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
RtDefs.rt_rom_view segs B W mem -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals: the caller discharges it by measurement *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:37) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Lemma cmd_asnprintf_of_sh : forall FF K gc gv img_lo img_hi cr pc,
  (forall ly S W regs mem md, ecall_pre segs B ly S W regs mem md -> RtDefs.rt_rom_view segs B W mem ->
    consts_view segs W mem cr) ->
  sh_asnprintf_realizes segs B FF K gc gv img_lo img_hi cr pc -> cmd_asnprintf_realizes FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc DV HS ly S W regs mem md d n f xs ws T cval Hpre HK HW R10 R11 R12 Hrom.
exact (HS ly S W regs mem md d n f xs ws T cval Hpre HK HW R10 R11 R12 (DV ly S W regs mem md Hpre Hrom)).
Qed.

(* ---- fuzz_command's two contracts at FR_cmd ---- *)
Definition asnprintf_sh (pc gotw guard : Z) : Prop :=
cmd_asnprintf_realizes FR_cmd CMD_SNP_K gotw guard CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR pc.
Definition asprintf_shU (pc gotw guard : Z) : Prop :=
sh_asprintf_realizesU FR_cmd CMD_SP_K gotw guard CMD_IMG_LO CMD_IMG_HI CMD_SP_CR pc.
Definition asprintf_sh (pc gotw guard : Z) : Prop :=
sh_asprintf_realizes FR_cmd CMD_SP_K gotw guard CMD_IMG_LO CMD_IMG_HI CMD_SP_CR pc.

Lemma asprintf_sh_of_U : forall pc gotw guard, asprintf_shU pc gotw guard -> asprintf_sh pc gotw guard.
Proof. intros pc gotw guard H. exact (sh_asprintf_of_U _ _ _ _ _ _ _ _ H). Qed.

End c.
End b.
