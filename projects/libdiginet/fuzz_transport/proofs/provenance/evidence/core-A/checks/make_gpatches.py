#!/usr/bin/env python3
"""make_gpatches.py STAGE_OUT OUT -- write the transport image-A core's G hunks as port_core --patch files.

STAGE_OUT  a port_core stage-out directory (holds A/<f>.v with the provenance line after the donor notice block)
OUT        output directory: OUT/g-<f>.patch (unified diff, `--- A/<f>.v` / `+++ A/<f>.v`, 3 lines of context, against
           the file WITHOUT its provenance line, the text port_core patches) and OUT/stage-g/A/<f>.v (the patched text)

Every edit names the exact old lines it replaces (by line number in the text without the provenance line); a
mismatch stops the script, so a re-run on a moved stage-out fails loudly instead of patching the wrong line.
The G hunks are libreac/fuzz_pcap's (origin/ossv/recipes 198234fa4d3) G-adapted driver hunks restated for
fuzz_transport (see GHUNKS-A.md): the program contract takes the slot's G (A/ACfn.v), the driver states its
call site at the harness globals' hull DRV_G (A/AD2f.v; DRV_G_LO / DRV_G_HI and region_avoids_G are the start-up
layer's A/AD1y.v, cut around the hull: libdiginet/fuzz_transport lib/A/AD1y.v (file sha256 cd08f8cdb321; donor not released)) and reads the call's journal
through A/TransportDrvG.v. On the cut start-up list the hull clip changes no region, so no count moves (as in pcap)."""
import os
import re
import subprocess
import sys
import tempfile

PROV = re.compile(r'^\(\* Relocated from proofs/\S+ at [0-9a-f]{12} by port_core [0-9a-f]{12} onto \S+ \((plain|ubsan|asan|asan-ubsan)\)\. \*\)$')
M = 'OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib'
CLIP_G = ('flat_map (clip_out DRV_G_LO DRV_G_HI) (flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r))')
CLIP_0 = 'flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)'

# file -> list of (first line, [old lines], [new lines]); line numbers in the text without the provenance line
EDITS = {
    'ACfn': [
        (16, [f'From {M}.Reusable Require Import YC5d.'],
         [f'From {M}.Reusable Require Import YC5d.',
          f'From {M}.A Require Import W_journalG.']),
        (28, ['Variable B : asyms.'],
         ['(* The program-global ranges G the call may change (the harness globals): W_journalG.v\'s ajournal_gx G. The slot',
          '   states its contract at its own G; the driver states its call site at the hull DRV_G (A/AD2f.v, A/TransportDriver.v). *)',
          'Variable G : list (Z * Z).',
          'Variable B : asyms.']),
        (51, ["ajournal segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\\ k <= EV_LIB /\\"],
         ["ajournal_gx segs B G 0 [] LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\\ k <= EV_LIB /\\"]),
        (72, ['Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=',
              'forall fx : YK11.FPState, @tfib_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.'],
         ['Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (G : list (Z * Z)) (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=',
          'forall fx : YK11.FPState, @tfib_lib_contract_x fx rc LS G B MT XM_LIB XN_LIB RLO RHI.']),
    ],
    'AD1w': [
        (12, [f'From {M}.A Require Import AE2k AD1u.'],
         [f'From {M}.A Require Import AE2k AD1u.',
          f'From {M}.A Require Import W_journalG.']),
        (97, ["YCbq.ajournal tfibsegs B LLVMF_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k /\\ k <= EV_LIB /\\"],
         ['(* the call\'s journal: W_journalG.v\'s ajournal_gx at the harness globals\' hull DRV_G (A/AD2f.v), no out window *)',
          "ajournal_gx tfibsegs B DRV_G 0 [] LLVMF_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k /\\ k <= EV_LIB /\\"]),
    ],
    'AD1m': [
        (32, ['Hypothesis LIBC : tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.'],
         ['(* the program contract at the harness globals\' hull DRV_G (A/AD2f.v); A/TransportDriver.v lifts the slot\'s G to it *)',
          'Hypothesis LIBC : tfib_lib_contract_x DRV_G B MT XM_LIB XN_LIB RLO RHI.']),
    ],
    'AD1p': [
        (50, ['Hypothesis LIBC : tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.'],
         ['(* the program contract at the harness globals\' hull (A/AD2f.v DRV_G), as A/AD1m.v states it *)',
          'Hypothesis LIBC : tfib_lib_contract_x AD2f.DRV_G B MT XM_LIB XN_LIB RLO RHI.']),
    ],
    'AD1q': [
        (21, [f'From {M}.A Require Import ACfn AD1p.'],
         [f'From {M}.A Require Import ACfn AD1p.',
          f'From {M}.A Require Import TransportDriver.']),
        (40, ['Hypothesis LIBX : tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI.'],
         ['(* The program-global ranges G the call may write (the slot\'s, the harness globals), inside the hull of A/AD2f.v:',
          '   the slot proves its contract at G and A/TransportDriver.v lifts it to the hull the driver states its call at. *)',
          'Variable G : list (Z * Z).',
          'Hypothesis G_HULL : g_in_hull G.',
          'Hypothesis LIBX : tfib_lib_contract_x_all G B MT XM_LIB XN_LIB RLO RHI.']),
        (68, ['Proof. exact (tfib_drv_main B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (LIBX _) xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS). Qed.'],
         ['Proof. exact (tfib_drv_main B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (tfib_lib_contract_x_all_hull G B MT XM_LIB XN_LIB RLO RHI G_HULL LIBX _) xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS). Qed.']),
    ],
    'AD1r': [
        (160, [f'From {M}.A Require Import AE2k AD1u.'],
         [f'From {M}.A Require Import AE2k AD1u TransportDrvG.']),
        (226, ["Lemma journal_regions_kept : forall E rs ly S (W : world tfibsegs) mem md ly' S' W' mem' md' k sp0,",
               "YCbq.ajournal tfibsegs B LLVMF_STK sp0 [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k ->"],
         ["Lemma journal_regions_kept : forall E rs ly S (W : world tfibsegs) mem memS md ly' S' W' mem' md' k sp0,",
          "YCbq.ajournal tfibsegs B LLVMF_STK sp0 [YI16.sink_token] ly S W memS md [] ly' S' W' mem' md' k ->",
          '(forall a, 0 <= a < 2 ^ 64 -> ~ (DRV_G_LO <= a < DRV_G_HI) -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a) ->']),
        (232, ['forallb (drv_keep_ok (-208)) rs = true ->'],
         ['forallb (drv_keep_ok (-208)) rs = true -> forallb region_avoids_G rs = true ->']),
        (236, ["intros E rs ly S W mem md ly' S' W' mem' md' k sp0 HJ Hh0 Hh1 HAR Hwf Hok Hchk E0 E6 Hsp0 HCT."],
         ["intros E rs ly S W mem memS md ly' S' W' mem' md' k sp0 HJ Hag Hh0 Hh1 HAR Hwf Hok Hchk HavG E0 E6 Hsp0 HCT."]),
        (238, ['pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.'],
         ['pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.']),
        (244, ['pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.'],
         ['pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.',
          'pose proof (proj1 (forallb_forall _ _) HavG r Hr) as HrG.']),
        (248, ['{ intros a Ha.'],
         ['{ intros a Ha.',
          'assert (NG : ~ (DRV_G_LO <= a < DRV_G_HI)) by (apply drv_keep_not_G; unfold drv_keep_set; right; right; right; right; lia).']),
        (250, ['{ apply F1; [lia | unfold LLVMF_STK; lia]. }'],
         ['{ rewrite <- (Hag a ltac:(lia) NG). apply F1; [lia | unfold LLVMF_STK; lia]. }']),
        (278, ['apply (mbyte_of_aview tfibsegs). apply F3; [exact Himg | rewrite (ts_owned B HB); exact Hno | rewrite Eerr; exact Hne |].'],
         ['assert (NG : ~ (DRV_G_LO <= YP09.c_off c + i < DRV_G_HI)) by (apply (region_avoids_G_sound r); [exact HrG | exact Hb | lia]).',
          'apply (mbyte_of_aview tfibsegs). rewrite <- (Hag (YP09.c_off c + i) ltac:(lia) NG).',
          'apply F3; [exact Himg | rewrite (ts_owned B HB); exact Hno | rewrite Eerr; exact Hne |].']),
        (291, ["Lemma lib_reseat : forall E (W W' : world tfibsegs) regs mem regs' mem' ly S md ly' S' md' k,"],
         ["Lemma lib_reseat : forall E (W W' : world tfibsegs) regs mem memS regs' mem' ly S md ly' S' md' k,"]),
        (294, ["YCbq.ajournal tfibsegs B LLVMF_STK (usp - 208) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k ->"],
         ["YCbq.ajournal tfibsegs B LLVMF_STK (usp - 208) [YI16.sink_token] ly S W memS md [] ly' S' W' mem' md' k ->",
          '(forall a, 0 <= a < 2 ^ 64 -> ~ (DRV_G_LO <= a < DRV_G_HI) -> aview tfibsegs (w_H W) memS a = aview tfibsegs (w_H W) mem a) ->']),
        (300, ["intros E W W' regs mem regs' mem' ly S md ly' S' md' k HS E0 E6 HJ Hh0 Hh1 HAR HP Ha0 HCT."],
         ["intros E W W' regs mem memS regs' mem' ly S md ly' S' md' k HS E0 E6 HJ Hag Hh0 Hh1 HAR HP Ha0 HCT."]),
        (301, ['pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.'],
         ['pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.',
          'pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.']),
        (323, ['* pose proof Hr0 as (_ & _ & RW & _). cbn [r_wlo r_whi r_base base_val WIN208] in RW. rewrite E0 in RW.'],
         ['* pose proof Hr0 as (_ & _ & RW & _). cbn [r_wlo r_whi r_base base_val WIN208] in RW. rewrite E0 in RW.',
          'assert (NG : ~ (DRV_G_LO <= usp + o < DRV_G_HI)) by (apply drv_keep_not_G; unfold drv_keep_set; right; right; right; right; unfold sp_window_lo in Ulo; lia).']),
        (325, ['{ apply F1; [unfold sp_window_lo in Ulo; lia | lia]. }'],
         ['{ rewrite <- (Hag (usp + o) ltac:(unfold sp_window_lo in Ulo; lia) NG). apply F1; [unfold sp_window_lo in Ulo; lia | lia]. }']),
        (330, ["+ exact (journal_regions_kept E (tl L_mem) ly S W mem md ly' S' W' mem' md' k (usp - 208) HJ Hh0 Hh1 HAR (proj2 (andb_prop _ _ Hwf)) Hrs0",
               'ltac:(vm_compute; reflexivity) E0 E6 eq_refl HCT).'],
         ["(* the kept image regions avoid the harness globals' hull: A/AD2f.v's L_mem_avoids_G (region_avoids_G on tl L_mem) *)",
          "+ exact (journal_regions_kept E (tl L_mem) ly S W mem memS md ly' S' W' mem' md' k (usp - 208) HJ Hag Hh0 Hh1 HAR (proj2 (andb_prop _ _ Hwf)) Hrs0",
          'ltac:(vm_compute; reflexivity) L_mem_avoids_G E0 E6 eq_refl HCT).']),
        (656, ["intros l W' c' _ HAI' (ly' & S' & regs' & mem' & md' & k & -> & HJ & Hk & HP & Ha0' & HPERM & Hfdl & Hmfs' & Hret & Hout & Hsorted & Hnames' & HFI' & Hplk). cbn [cfg_model] in HAI'.",
               'unfold cfg_at.'],
         ["intros l W' c' _ HAI' (ly' & S' & regs' & mem' & md' & k & -> & HJG & Hk & HP & Ha0' & HPERM & Hfdl & Hmfs' & Hret & Hout & Hsorted & Hnames' & HFI' & Hplk). cbn [cfg_model] in HAI'.",
          'unfold cfg_at.',
          "(* the call's journal at the harness globals' hull (A/AD1w.v) is the donor's journal from a start memory memS that",
          '   agrees with mem outside the hull (A/TransportDrvG.v) *)',
          'apply drv_journal_of_gx in HJG as (memS & HJ & Hag).']),
        (665, ["{ apply (so_state_keep xst XFR j (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. destruct (STDOUT_static a Ha) as (H1 & H2 & H3). exact (F3 a H1 H2 H3 (spares_stdout a Ha)). }"],
         ["{ apply (so_state_keep xst XFR j (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. destruct (STDOUT_static a Ha) as (H1 & H2 & H3).",
          'rewrite (F3 a H1 H2 H3 (spares_stdout a Ha)).',
          'apply Hag; [unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha; lia | apply drv_keep_not_G; unfold drv_keep_set; right; left; exact Ha]. }']),
        (667, ["{ apply (arodata_keep (w_H W) (w_H W') mem mem'); [| exact HRO]. intros a H1 H2 H3. apply F3; [| exact H2 | exact H3 | exact (spares_ro a H1)]. apply in_img_hull. pose proof (in_ro_range a H1). lia. }"],
         ["{ apply (arodata_keep (w_H W) (w_H W') mem mem'); [| exact HRO]. intros a H1 H2 H3. pose proof (in_ro_range a H1).",
          'rewrite (F3 a); [| apply in_img_hull; lia | exact H2 | exact H3 | exact (spares_ro a H1)].',
          'apply Hag; [lia | apply drv_keep_not_G; unfold drv_keep_set; right; right; left; exact H1]. }']),
        (679, ["pose proof (lib_reseat E W W' regs mem regs' mem' ly S md ly' S' md' k HS E0 E6 ltac:(rewrite <- Hsp'; exact HJ) (proj2 (proj2 HFI)) (proj2 (proj2 HFI')) HAR HP Ha0' HCT) as HS2."],
         ["pose proof (lib_reseat E W W' regs mem memS regs' mem' ly S md ly' S' md' k HS E0 E6 ltac:(rewrite <- Hsp'; exact HJ) Hag (proj2 (proj2 HFI)) (proj2 (proj2 HFI')) HAR HP Ha0' HCT) as HS2."]),
    ],
    'AD2f': [
        (147, ['Definition SOBUF_LO : Z := 0x6141f8.   Definition SOBUF_HI : Z := 0x614608.'],
         ['Definition SOBUF_LO : Z := 0x6141f8.   Definition SOBUF_HI : Z := 0x614608.',
          "(* The harness globals' hull [DRV_G_LO, DRV_G_HI) (A/AD1y.v: g_cfg [0x5df080, +60) to OW [0x5f3060, +304)) as a",
          "   list of program-global ranges (W_journalG.v's G): the bytes the driver lets the PROGRAM call change. The loop",
          '   state kept across that call leaves the hull out: IMG_L, IMG_LC and L_pieces clip it out after STDOUT and SOBUF,',
          '   outermost. On the start-up list A/AD2j.v, cut around the hull, no region meets it, so the clip changes none. *)',
          'Definition DRV_G : list (Z * Z) := [(DRV_G_LO, DRV_G_HI - DRV_G_LO)].']),
        (152, [f'Definition IMG_L : smem := Eval vm_compute in flat_map (fun r => {CLIP_0}) IMG_B.',
               f'Definition IMG_LC : smem := Eval vm_compute in flat_map (fun r => {CLIP_0}) IMG_E.'],
         [f'Definition IMG_L : smem := Eval vm_compute in flat_map (fun r => {CLIP_G}) IMG_B.',
          f'Definition IMG_LC : smem := Eval vm_compute in flat_map (fun r => {CLIP_G}) IMG_E.']),
        (179, [f'++ map (fun r => {CLIP_0}) IMG_E ++ [ []; []; []; []; [] ].'],
         [f'++ map (fun r => {CLIP_G}) IMG_E ++ [ []; []; []; []; [] ].']),
        (285, ['Lemma IMG_L_wf : regions_wf IMG_L = true. Proof. reflexivity. Qed.'],
         ['Lemma IMG_L_wf : regions_wf IMG_L = true. Proof. reflexivity. Qed.',
          "(* Every image region of the loop state avoids the harness globals' hull. `tl` drops the stack window WIN208 (base",
          '   Some 0, which region_avoids_G (A/AD1y.v) passes anyway); A/AD1r.v walks tl L_mem. *)',
          'Lemma L_mem_avoids_G : forallb region_avoids_G (tl L_mem) = true.',
          'Proof. vm_compute. reflexivity. Qed.']),
    ],
}
ORDER = ['ACfn', 'AD1w', 'AD1m', 'AD1p', 'AD1q', 'AD1r', 'AD2f']


def strip_prov(lines):
    hits = [i for i, l in enumerate(lines) if PROV.match(l)]
    if len(hits) != 1:
        sys.exit(f'make_gpatches: expected one provenance line, found {len(hits)}')
    return lines[:hits[0]] + lines[hits[0] + 1:]


def main():
    so, out = sys.argv[1], sys.argv[2]
    os.makedirs(os.path.join(out, 'stage-g', 'A'), exist_ok=True)
    for f in ORDER:
        raw = open(os.path.join(so, 'A', f + '.v')).read()
        assert raw.endswith('\n')
        old = strip_prov(raw[:-1].split('\n'))
        new = list(old)
        for start, want, repl in sorted(EDITS[f], key=lambda e: -e[0]):
            got = new[start - 1:start - 1 + len(want)]
            if got != want:
                sys.exit(f'make_gpatches: {f}.v:{start}: old text differs\n  want {want!r}\n  got  {got!r}')
            new[start - 1:start - 1 + len(want)] = repl
        open(os.path.join(out, 'stage-g', 'A', f + '.v'), 'w').write('\n'.join(new) + '\n')
        with tempfile.NamedTemporaryFile('w', suffix='.v') as a:
            a.write('\n'.join(old) + '\n')
            a.flush()
            r = subprocess.run(['diff', '-u', '--label', f'A/{f}.v', '--label', f'A/{f}.v', a.name,
                                os.path.join(out, 'stage-g', 'A', f + '.v')], capture_output=True, text=True)
        if r.returncode != 1:
            sys.exit(f'make_gpatches: diff of {f}.v exited {r.returncode}: {r.stderr}')
        text = r.stdout
        open(os.path.join(out, f'g-{f}.patch'), 'w').write(text)
        print(f'g-{f}.patch\t{len(EDITS[f])} edits\t{sum(1 for l in text.splitlines() if l.startswith("@@"))} hunks')


main()
