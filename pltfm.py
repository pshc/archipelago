from base import *
import os
import subprocess

IOS_VERSION = '6.0'

TargetArch = DT('TargetArch', ('name', str),
                              ('ptrSize', int),
                              ('abiAttrs', str),
                              ('cc', str),
                              ('cFlags', [str]),
                              ('dataLayout', str),
                              ('targetTriple', str))

def host_arch():
    name = os.uname()[4]
    ptrSize, abiAttrs = {
        'x86': (4, ' nounwind ssp'),
        'x86_64': (8, ' uwtable nounwind ssp'),
    }[name]
    return TargetArch(name, ptrSize, abiAttrs, 'clang', [], '', '')

def iOS_dev_root():
    if os.sys.platform != 'darwin':
        print mark("This is an iOS target currently.")
    try:
        return subprocess.check_output(['xcode-select', '-print-path']).strip()
    except OSError, e:
        assert e.errno != 2, "Couldn't find xcode-select"
        raise

def arm_iOS_target():
    devRoot = iOS_dev_root()
    sysRoot = os.path.join(devRoot, 'Platforms', 'iPhoneOS.platform',
            'Developer', 'SDKs', 'iPhoneOS' + IOS_VERSION + '.sdk')

    cc = '/usr/local/bin/clang' # TEMP
    cFlags = ['-arch', 'armv7', '-miphoneos-version-min=' + IOS_VERSION,
            '-isysroot', sysRoot]
    dataLayout = "e-p:32:32:32-i1:8:32-i8:8:32-i16:16:32-i32:32:32-i64:32" + \
            ":64-f32:32:32-f64:32:64-v64:32:64-v128:32:128-a0:0:32-n32-S32"
    triple = "thumbv7-apple-ios%s.0" % (IOS_VERSION,)

    return TargetArch('arm', 4, ' nounwind', cc, cFlags, dataLayout, triple)

def i386_iOS_target():
    devRoot = iOS_dev_root()
    sysRoot = os.path.join(devRoot, 'Platforms', 'iPhoneSimulator.platform',
            'Developer', 'SDKs', 'iPhoneSimulator' + IOS_VERSION + '.sdk')

    cc = '/usr/local/bin/clang' # TEMP
    cFlags = ['-arch', 'i386', '-mios-simulator-version-min=' + IOS_VERSION,
            '-isysroot', sysRoot]
    triple = "i386-apple-ios%s.0" % (IOS_VERSION,)

    return TargetArch('i386', 4, ' nounwind', cc, cFlags, '', triple)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
