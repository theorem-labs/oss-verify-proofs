(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31 (the world relation R): aj_snprintf_at_xromR is the call-site rule over a
   journal at a reflexive and transitive world relation R (binders first; the call keeps the world, so no law of R is
   read); aj_snprintf_at_xrom keeps its statement and is the instance at wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSnp.v, with its module paths and module names changed; 317 of its 380 lines of code are new or changed and 199 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMsnprintfSx.v, with its module paths changed; 109 of its 155 lines of code are new or changed and 334 lines of the source are left out. *)
(* reac-pw/fuzz_segconf's snprintf and vsnprintf contracts (rows 4 and 5 of
   proofs/reac-pw/fuzz_segconf/provenance/evidence/interceptors/INTERFACE-A-interceptors.md), over a grammar
   that adds segconf's three conversions to the released one. Statements only; no walk, no proof.

   - The grammar. segconf's formats use literal bytes, %s, %d (released pieces) and %u, %zu, %.24s (not in the
     released grammar RtPFPf.v:8). RtPFPf.v, RtPFShared.v, RtPFSx.v and RtPFCmd.v are carried verbatim, so the
     released Inductive pf_piece stays as it is; seg_piece is a NEW type beside it: PRel p embeds every released
     piece, and Pu, Pzu, P24s are the new ones. A released per-piece proof stated over pf_piece (RT_pf_d.v,
     RT_pf_llu.v, FMpfArm*Seam.v, RT_pf_sh.v's arms) is untouched; at PRel p it is carried over by
     seg_step (PRel p) = pf_step p and the same format code. seg_parse reads a released code exactly as pf_parse does
     (the released branch is tried first at every byte), so seg_parse f = Some (map PRel ps) whenever
     pf_parse f = Some ps. (The constructor is not called SP: segconf's lib/Spec/SegModel.v has Notation SP := 32.)
   - The new pieces, with the text musl's printf_core writes and the argument shape the released predicates already
     state (pf_args_asan, RtPFShared.v:44-62, is reused unchanged):
       Pu   "%u"    one AInt v (a 32-bit int in a 64-bit slot, as RISC-V passes an unsigned int), text the decimal
                    digits of v mod 2^32 (GXA's model: PA_u (v mod 2^32), Printf_text.v:629 pt_conv_u);
       Pzu  "%zu"   one AU64 u (the 64-bit word), text the decimal digits of u (GXA's model: PA_ull u at T_SIZET,
                    Printf_text.v:616-621);
       P24s "%.24s" one APtr s, text firstn 24 s (musl: strnlen (s, 24) bytes). The precision is the fixed literal 24,
                    as the released grammar has fixed-width pieces (%04x, %02x) and no general width.
   - The family FR_seg lo hi has FR_cmd's eleven conjuncts in FR_cmd's order (RtPFCmd.v:90-95), over seg_parse,
     seg_text and seg_prec_pos, with RtPFCmd's own cmd_args_slack / cmd_args_amem; lo / hi are the image range the
     format lies in (FR_cmd: CMD_IMG_LO and the GOT word CMD_GOTW). seg_pk takes every piece, so FR_cmd rd rs f ws T
     gives FR_seg CMD_IMG_LO CMD_GOTW rd rs f ws T, and row 4 at RtPFCmd's constants gives
     RtFormat.asnprintf_realizes pc CMD_GOTW guard.
   - Row 4 (snprintf) is the released text RtPFCmd.cmd_asnprintf_realizes (RtPFCmd.v:310, the text of
     RtFormat.asnprintf_realizes, RtFormat.v:85) at FR_seg: no premise is new.
   - Row 5 (the vsnprintf wrapper, called by refuse with its own va_list): the released route proves the vsnprintf
     interceptor ONLY in the GXA-route form sh_avsnprintf_icpt_realizesUa (RtPFSx.v:166, FMsnprintfSvsni.v:981
     svsni_ok), which has four premises the frozen sh_avsnprintf_icpt_realizes (RtPFShared.v:226) lacks. So
     seg_avsnprintf_icpt_realizes is the Ua text at U = [] (ecall_pre, AR in the post), with ONE premise changed as
     cmd_asnprintf_realizes changes it: consts_view over cr becomes RtDefs.rt_rom_view (a call site has no AR for the
     runtime-owned read-only bytes; RtPFCmd.v:304-309).
   - The windows are kit constants, as in RtString.v: 2 * ESTACK at both entries. Measured on image A (pin sha256
     48c5355bdacb..., read from neutral excerpts of the pin): the trampolines are one `j` each
     (snprintf 0x43a64 -> 0x49054, vsnprintf 0x43a5c -> 0x48c64); frames ___interceptor_snprintf 96,
     ___interceptor_vsnprintf 2032 + 128, musl vsnprintf 304, ___interceptor_vfprintf 48, fuzz_command's numbers
     (RtPFCmd.v:33-36). snprintf: glue 2,608 + GXA's VF_DEPTH 5,552 = 8,160; vsnprintf: 2,512 + 5,552 = 8,064.
   - Every image number is a parameter: pc, gotw (the GOT word musl vfprintf loads its guard pointer from, image A
     0xa36d8: `ld s2` at 0x96c5c; also the formats' upper bound, as GXA reads a format as image data below that word,
     G_vfprintf_snf.v:210), guard, img_lo / img_hi (dest_off_globals, and img_lo the formats' lower bound), cr (the
     image's read-only ranges). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the pieces ---- *)
(* every released piece (PRel p), and segconf's three new conversions *)
Inductive seg_piece : Type := PRel (p : pf_piece) | Pu | Pzu | P24s.

(* RtPFPf.v:11-44 with three branches added: 'u' (117), 'z' 'u' (122 117), '.' '2' '4' 's' (46 50 52 115). At every
   byte the released branch is tried first. *)
Fixpoint seg_parse (f : list Z) : option (list seg_piece) :=
  match f with
  | [] => Some []
  | b :: r =>
    if b =? 37 then
      match r with
      | c :: r1 =>
        if c =? 100 then option_map (cons (PRel Pd)) (seg_parse r1)
        else if c =? 99 then option_map (cons (PRel Pc)) (seg_parse r1)
        else if c =? 115 then option_map (cons (PRel Ps)) (seg_parse r1)
        else if c =? 117 then option_map (cons Pu) (seg_parse r1)
        else if c =? 48 then
          match r1 with
          | c2 :: c3 :: r3 =>
              if (c2 =? 52) && (c3 =? 120) then option_map (cons (PRel Px04)) (seg_parse r3)
              else if (c2 =? 50) && (c3 =? 120) then option_map (cons (PRel Px02)) (seg_parse r3)
              else None
          | _ => None
          end
        else if c =? 108 then
          match r1 with
          | c2 :: c3 :: r3 =>
              if (c2 =? 108) && (c3 =? 117) then option_map (cons (PRel Pllu)) (seg_parse r3) else None
          | _ => None
          end
        else if c =? 122 then
          match r1 with
          | c2 :: r2 => if c2 =? 117 then option_map (cons Pzu) (seg_parse r2) else None
          | [] => None
          end
        else if c =? 46 then
          match r1 with
          | c2 :: c3 :: r3 =>
              if (c2 =? 42) && (c3 =? 115) then option_map (cons (PRel Pps)) (seg_parse r3)
              else if (c2 =? 50) && (c3 =? 52) then
                match r3 with
                | c4 :: r4 => if c4 =? 115 then option_map (cons P24s) (seg_parse r4) else None
                | [] => None
                end
              else None
          | _ => None
          end
        else None
      | [] => None
      end
    else if (0 <? b) && (b <? 256) then option_map (cons (PRel (PLit b))) (seg_parse r)
    else None
  end.

(* one piece: what it renders and the arguments it leaves; at PRel p the bodies are pf_text's (RtPFPf.v:73-86) *)
Definition seg_step (q : seg_piece) (args : list pf_arg) : option (list Z * list pf_arg) :=
  match q, args with
  | PRel (PLit b), _ => Some ([b], args)
  | PRel Pd, AInt v :: a' => Some (pf_dec v, a')
  | PRel Pc, AInt v :: a' => Some ([v mod 256], a')
  | PRel Px04, AInt v :: a' => Some (pf_hex4 v, a')
  | PRel Px02, AInt v :: a' => Some (pf_hex2 v, a')
  | PRel Pllu, AU64 u :: a' => Some (pf_udec u, a')
  | PRel Ps, APtr s :: a' => Some (s, a')
  | PRel Pps, AInt k :: APtr s :: a' =>
      if (0 <=? k) && (k <=? Z.of_nat (length s)) then Some (firstn (Z.to_nat k) s, a') else None
  | Pu, AInt v :: a' => Some (pf_udec (v mod 2 ^ 32), a')
  | Pzu, AU64 u :: a' => Some (pf_udec u, a')
  | P24s, APtr s :: a' => Some (firstn 24 s, a')
  | _, _ => None
  end.

(* the text: the steps one after the other, every argument consumed *)
Fixpoint seg_text (qs : list seg_piece) (args : list pf_arg) : option (list Z) :=
  match qs with
  | [] => match args with [] => Some [] | _ :: _ => None end
  | q :: qs' =>
      match seg_step q args with
      | Some (c, a') => option_map (app c) (seg_text qs' a')
      | None => None
      end
  end.

(* every %.*s precision is at least 1 (RtPFShared.v:84-92 pf_prec_pos; the new pieces take one argument each) *)
Fixpoint seg_prec_pos (qs : list seg_piece) (args : list pf_arg) : Prop :=
  match qs, args with
  | [], _ => True
  | PRel (PLit _) :: qs', _ => seg_prec_pos qs' args
  | PRel Pps :: qs', AInt k :: _ :: a' => 1 <= k /\ seg_prec_pos qs' a'
  | PRel Pps :: _, _ => True
  | _ :: qs', _ :: a' => seg_prec_pos qs' a'
  | _ :: _, [] => True
  end.

(* ---- the family ---- *)
(* every piece: the released pieces (PRel _: literal bytes, %d, %c, %04x, %02x, %llu, %s, %.*s) and segconf's new ones
   (%u, %zu, %.24s), so that FR_cmd is a special case of FR_seg (found by the fresh review of these texts) *)
Definition seg_pk (q : seg_piece) : Prop :=
  match q with PRel _ | Pu | Pzu | P24s => True end.

(* FR_cmd's shape (RtPFCmd.v:90-95) over seg_parse / seg_text for the conversions PK covers, the format a nonempty
   literal in [lo, hi) *)
Definition seg_fam (PK : seg_piece -> Prop) (lo hi : Z) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (qs : list seg_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ seg_parse fmt = Some qs /\ Forall PK qs /\ pf_args_asan rd rs ws args /\
    seg_text qs args = Some T /\ seg_prec_pos qs args /\
    lo <= f /\ f + Z.of_nat (length fmt) + 1 <= hi /\ cmd_args_slack ws args /\
    fmt <> [] /\ cmd_args_amem ws args.

(* segconf's family *)
Definition FR_seg (lo hi : Z) : fmt_fam := seg_fam seg_pk lo hi.

(* the windows at the two entries (header: 8,160 and 8,064 bytes on image A) *)
Definition SEG_SNP_K : Z := 2 * ESTACK.
Definition SEG_VSN_K : Z := 2 * ESTACK.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* ---- the vsnprintf wrapper (d, n, f, ap), the arguments the words at ap: RtPFSx.v:166 sh_avsnprintf_icpt_realizesUa
   with U = [] (RtPFShared.v:226's ecall_pre and AR) and consts_view over cr replaced by RtDefs.rt_rom_view;
   every other line is the Ua text's ---- *)
Definition seg_avsnprintf_icpt_realizes (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S W regs mem md d n f ap (ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 ap ->
RtDefs.rt_rom_view segs B W mem -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
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
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---- the two rows a walker takes ---- *)
(* Row 4. snprintf (d, n, f, ...) at the trampoline pc: RtFormat.asnprintf_realizes's text (RtPFCmd.cmd_asnprintf_realizes,
   RtPFCmd.v:310) at segconf's family, formats in [img_lo, gotw) *)
Definition seg_asnprintf_realizes (img_lo img_hi : Z) (cr : list (Z * Z)) (pc gotw guard : Z) : Prop :=
cmd_asnprintf_realizes segs B (FR_seg img_lo gotw) SEG_SNP_K gotw guard img_lo img_hi cr pc.

(* Row 5. vsnprintf (d, n, f, ap) at the trampoline pc, with the caller's va_list ap *)
Definition seg_avsnprintf_realizes (img_lo img_hi : Z) (cr : list (Z * Z)) (pc gotw guard : Z) : Prop :=
seg_avsnprintf_icpt_realizes (FR_seg img_lo gotw) SEG_VSN_K gotw guard img_lo img_hi cr pc.
End c.
End b.
